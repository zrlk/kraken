/-
**`ChildPrem.hsvc` at the clone's data** (AArch64; the `hCP` call site): at main's
`clone` over the placed layout (`PreRH` at `(LH hp i).Λ`), under `VBufR`, `print`'s `write` in the child meets
`PI`'s memory side (`hsvc_I`) at the clone's words `wordsX th`: the slice's buffer is `lBH`
(`HelloNewBuf.clonePreH_labels`), placed at main's `x9` (`HelloPreA.hsvc_clone`), whose 13 bytes fit
(`HelloCloneMem.x9_fit_preRH`).

- `hsvc_preRH`: `SvcX … (wordsX th) tp w0 w1 w2 w3 w4 13 2` at the record's placement and `msWH`.
-/
import Spike.Lib.HelloChildSvcI
import Spike.Lib.HelloChildSvcClone
import Spike.Lib.A64HelloCloneMem
import Spike.Lib.HelloCPWords

namespace Spike.Lib.HelloAssemblyI

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Spike.Lib Spike.Lib.WakeA64
open Spike.Lib.HelloMsW (msWH)
open Spike.Lib.HelloSpawnR (PreRH)
open Spike.Lib.HelloOkW (lBH)
open Spike.Lib.A64.Flow.Worker.Hello.SegR (wordsX SvcX)
open SccCode (helloProg)

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- **`ChildPrem.hsvc` at `PreRH`** (module doc). -/
theorem hsvc_preRH (ho : o.prog = helloProg) (G0 : ιH hp i → Loc → Val → Prop) {arch : WeakMem.Arch}
    {R1 : Cfg → TermRun.Cfg → Prop} {cT : ιH hp i → Loc} {cS : ιH hp i → WeakMem.Address} {pT : ιH hp i → Loc}
    {Pa : ιH hp i → Spike.Lib.Inv2Core.Inv2Params isaLSE2} {G : ιH hp i → Loc → Val → Prop}
    {passT : State → Prop} {M : Spike.Lib.WakeM0.MSide (ιH hp i)} {D : HelloW1.WSideH (ιH hp i)}
    {r0 r1 : ιH hp i → Scc.Sem.Range} {w : ιH hp i} {d : Cfg} {th : Thread isaLSE2} {stack : Nat}
    {s s' : TermRun.Cfg} {s0 s1 : TermRun.TTh} {lbl : WeakMem.AllocLabel → Option Nat}
    {lsize : WeakMem.AllocLabel → Nat} {ts : Nat → Option Nat} {j : Nat} {own₀ : List (Loc × Val)}
    {l : WeakMem.AllocLabel} (hv : HelloVBuf.VBufR s)
    (hR : PreRH arch R1 (SRH hp i) cT cS pT Pa G passT M D r0 r1 (LH hp i).Λ w d th stack s s' s0 s1 lbl lsize ts j
      own₀ l)
    {F : MachineData → Prop} {tp : BitVec 64} {w0 w1 w2 w3 w4 : TermRun.Word}
    (h0 : w0.val = .loc ⟨lBH, 0⟩ 0) (h2 : w2.val = .num 13) :
    SvcX (LH hp i).exe (endH hp i) (LH hp i).pfx (SRH hp i w).lbl
      (fun _ => msWH (LH hp i) (GH hp i G0) (SRH hp i) w) F (wordsX th) tp w0 w1 w2 w3 w4 13 2 := by
  obtain ⟨X, hC⟩ := hR.clone
  have hth := hR.pre.threads
  obtain ⟨lb, ⟨th0, hd, l', hs, hS⟩, -, -, hl, -, hfit, hlen⟩ :=
    HelloPreA.hsvc_clone hC hth (HelloCloneMem.x9_fit_preRH hR hC)
  obtain ⟨th0', hd', l'', lb', ws, hs', hS', hh, rfl, -, -⟩ := HelloNewBuf.clonePreH_labels hv hC
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
    rfl
  subst hlb
  rw [← HelloSpawnR.lbl_clone hR] at hl
  exact hsvc_I hp i ho G0 w h0 hl h2 hfit hlen

end Inst

end Spike.Lib.HelloAssemblyI

/-- info: 'Spike.Lib.HelloAssemblyI.hsvc_preRH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloAssemblyI.hsvc_preRH
