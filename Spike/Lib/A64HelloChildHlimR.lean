/-
**The child's limit-word premises at the root's clone data** (AArch64, the residual of
the child's stack-limit premises): `Hello.SegR.ChildPrem`'s `hlimT`/`hlimW` exactly as the root's `hCP` asks them
(`A64HelloRootInv.hello_root_inv`'s `hCP`): at the worker's memory side `HelloMsW.msWH (LH hp i) (GH hp i (G0H hp i))
(SRH hp i) w`, the frame `DFrame (childR stack (-272)) (childAfter abi x tid th stack tls).st.st.1`, the thread
pointer `ofNat tls` and the stack `ofNat stack`.

The chain: `HelloTcbArea.tlsTcb_H` (`TcbArea` at main's second `scc_rt_alloc_tcb`, `TlsTcb` at the second
take `r1Of`) at `msH`; `TlsTcb` is read only through `rt`, `mp`, `G`, which `msWH` (`msH.withBW`) keeps; then
`HelloChildTls.TlsTcb.hlim_stack` at the clone's held list and top, the second take not wrapping
(`HelloChildTcb.hbd_of`).

- `tlsTcb_msWH`: `TlsTcb` at `msH` is `TlsTcb` at `msWH`.
- `hlim_cloneH`: `hlimT ∧ hlimW` at the root's data. Premises, all at the root's clone:
  - `hpin3` (`HelloTcbArea.hpin3_H hp i CertFacts.pinZ_helloCert (by decide)`), `hinit2` (the second limit word's
    initial value, a loader fact as wake's `A64WakeRoot`'s), `hsub1` (`StartPlaceLy.hsub1_W hp i hA13`);
  - `hm`: the memory relation at the record's placement (`PreRH.pre.inv1.mem`, after `PreRH.pre.SR`);
  - `hheld`, `htop`: `PreRH.pre.held`, `PreRH.pre.top` (`r1 := fun _ => r1Of (LH hp i).lab`);
  - `htls`: the clone's thread pointer the second TCB `tH` (clone side: `ClonePreH` gives
    `tls = x3`, and `HelloTcbArea.x3_of_cloneMidH` gives `x3 = tH` at `CloneMidH`).
-/
import Spike.Lib.A64HelloTcbArea
import Spike.Lib.A64HelloChildTcb
import Spike.Lib.HelloMsW

namespace Spike.Lib.HelloChildHlimR

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (MemRelP Range)
open Scc.Sem.Kernel (KState)
open Spike.Lib.Handover (childAfter)
open Spike.Lib.A64.Rt.PreChild (r1Of)
open Spike.Lib.A64.Flow (tcbA DFrame)
open Spike.Lib.A64.Flow.Worker.Wake.Child (childR)
open Spike.Lib.A64.Flow.Worker.Hello.Child (wcJE Words)
open Spike.Lib.A64.PhRec (m0Of)
open Spike.Lib.HelloGOf2H (lim2AH)
open Spike.Lib.HelloMs (msH)
open Spike.Lib.HelloMsW (msWH)
open Spike.Lib.HelloAssemblyI (LH ιH SRH GH)
open Spike.Lib.HelloAssemblyIM (G0H)
open Spike.Lib.A64.Flow.HelloWc (tcb2QH tH)
open Spike.Lib.HelloChildTls (TlsTcb)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
    (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- **`TlsTcb` at `msH` is `TlsTcb` at `msWH`** (`msWH` is `msH` with `bo`, `we` set; `TlsTcb` reads `rt`, `mp`,
`G`). -/
theorem tlsTcb_msWH {G : ιH hp i → Loc → Val → Prop} {w : ιH hp i} {q : Spike.Lib.A64.Rt.TcbGG} {tls : Nat}
    {r1 : Range} (h : TlsTcb (msH (LH hp i) G (SRH hp i) w) (LH hp i).lab q tls r1) :
    TlsTcb (msWH (LH hp i) G (SRH hp i) w) (LH hp i).lab q tls r1 :=
  have ⟨⟨a, b, c, d, e, f, g⟩, h2, h3, h4, h5⟩ := h
  ⟨⟨a, b, c, d, e, f, g⟩, h2, h3, h4, h5⟩

/-- **`ChildPrem.hlimT` and `hlimW` at the root's clone data** (module doc): the worker's memory side `msWH`,
the thread pointer the second TCB `tH`, the stack the second take's top, held first for `tid`. -/
theorem hlim_cloneH
    (hpin3 : (LH hp i).pinA.toNat + 176 ≤ (LH hp i).Λ.pinned.lo + (LH hp i).Λ.pinned.size)
    (hinit2 : (m0Of (LH hp i).Λ o.prog o.secs).initVal ⟨lim2AH (LH hp i), 8⟩ = 0)
    (hsub1 : (r1Of (LH hp i).lab).Sub (LH hp i).Λ.stackPool)
    (w : ιH hp i) {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tp tq sp : List Nat}
    (hm : MemRelP (LH hp i).Λ (SRH hp i w).lbl (SRH hp i w).lsize ts tm sm tp tq sp)
    {x : KState} {tid : Nat} {th : Thread isaLSE2} {stack tls : Nat} {r0 : Range}
    (hheld : x.held = [(tid, r1Of (LH hp i).lab), (tid, r0)])
    (htop : (r1Of (LH hp i).lab).lo + (r1Of (LH hp i).lab).size = stack)
    (htls : tls = (tH (LH hp i).lab).toNat) :
    (∀ r : Reg64s, r.TPIDR_EL0.toBitVec = BitVec.ofNat 64 tls →
      (msWH (LH hp i) (GH hp i (G0H hp i)) (SRH hp i) w).rt (tcbA r 8).toNat ∧
      (msWH (LH hp i) (GH hp i (G0H hp i)) (SRH hp i) w).mp ⟨tcbA r 8, 8⟩ false ∧
      (∀ m, DFrame (childR stack (-272)) (childAfter Scc.Sem.A64.abi x tid th stack tls).st.st.1 m →
        Mem.loadInt m.dmem (tcbA r 8) 8 = none) ∧
      ∀ v : Val, (msWH (LH hp i) (GH hp i (G0H hp i)) (SRH hp i) w).G ⟨tcbA r 8, 8⟩ v →
        (v.setWidth 64).toNat ≤ (BitVec.ofNat 64 stack - (80 : Int64).toBitVec).toNat) ∧
    ∀ {c0 : Spike.Lib.Ctl} {w' : Words} x29 ra σ c, wcJE c0 w' x29 ra (BitVec.ofNat 64 tls) σ c →
      σ.regs.SP.toBitVec = BitVec.ofNat 64 stack - (80 : Int64).toBitVec →
      (msWH (LH hp i) (GH hp i (G0H hp i)) (SRH hp i) w).rt (tcbA σ.regs 8).toNat ∧
      (msWH (LH hp i) (GH hp i (G0H hp i)) (SRH hp i) w).mp ⟨tcbA σ.regs 8, 8⟩ false ∧
      (∀ m, DFrame (childR stack (-272)) (childAfter Scc.Sem.A64.abi x tid th stack tls).st.st.1 m →
        Mem.loadInt m.dmem (tcbA σ.regs 8) 8 = none) ∧
      ∀ v : Val, (msWH (LH hp i) (GH hp i (G0H hp i)) (SRH hp i) w).G ⟨tcbA σ.regs 8, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.SP.toBitVec - (96 : Int64).toBitVec).toNat := by
  have hT := tlsTcb_msWH hp i (Spike.Lib.HelloTcbArea.tlsTcb_H hp i hpin3 hinit2 hsub1 w hm
    ⟨0#64, 0#64, 0#64⟩ ⟨Spike.Lib.HelloMainPreSrc.newTerm, [], none⟩ htls)
  have hbd := Spike.Lib.HelloChildTcb.hbd_of (LH hp i) hsub1
  have hlo1 : (r1Of (LH hp i).lab).lo = (Spike.Lib.A64.Flow.Ret0.stacksA (LH hp i).lab).toNat + 16384 := by
    show (Spike.Lib.A64.Flow.Ret0.stacksA (LH hp i).lab + 16384#64).toNat = _
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by simp only [BitVec.toNat_ofNat]; omega)]; rfl
  have hsz : (r1Of (LH hp i).lab).size = 16384 := rfl
  exact hT.hlim_stack (t := th) htop hheld (by omega) (by omega)

/-- `hlim_cloneH`'s thread-pointer premise is met by the second TCB itself, and its held list and top by the
clone's (`SpawnPreH.held`, `top`): the premises are jointly satisfiable. -/
example (lab : Label → Int64) (r0 : Range) :
    ∃ (x : KState) (stack tls : Nat), x.held = [(0, r1Of lab), (0, r0)] ∧
      (r1Of lab).lo + (r1Of lab).size = stack ∧ tls = (tH lab).toNat :=
  ⟨{ slots := #[], held := [(0, r1Of lab), (0, r0)] }, _, _, rfl, rfl, rfl⟩

end Spike.Lib.HelloChildHlimR

/-- info: 'Spike.Lib.HelloChildHlimR.tlsTcb_msWH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloChildHlimR.tlsTcb_msWH

/-- info: 'Spike.Lib.HelloChildHlimR.hlim_cloneH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloChildHlimR.hlim_cloneH
