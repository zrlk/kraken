/-
**hello's stack bounds wired in**: the bounds of
`Spike/Lib/A64HelloStackB.lean` at the two premises they discharge.

- 5f' (main): `wcWf_W2Hb`, `WcW2.wcWf_W2H` with `wcMidW_wcGH`'s band `hband` from `BoxPureH`'s `R.base + 80` the
  first stack's top (`StackB.bandTiH_of`), the form `HelloRootInst.h0W_I` holds it in (`hB.2.2.2.2.2.1`).
- 5f (thread): `childP_of_cloneR1`, `SegR.childP_of_clone` at the runtime's second stack `r1Of L.lab`, its three
  bounds (`htop`, `hal`, `hsz`) from its place in the pool (`StackB.childB_r1Of`, `HelloRootBase.hsub`).
-/
import Spike.Lib.A64HelloStackB
import Spike.Lib.A64HelloWcW2
import Spike.Lib.A64HelloWorkerSegP

namespace Spike.Lib.A64.HelloPh.WcW2

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib (Arena FragS Ctl Region)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.Rt.Reserve (ntA)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64ConsumerS (PlacedSE)
open Spike.Lib.A64.Flow.HelloWc (WcMainWH tH)
open Spike.Lib.A64.HelloPh.RootWX (W2H)
open Spike.Lib.HelloHMid (SBH QBH)

section Main

variable {L : RuntimeLayout} {ar : Arena} {Dt : State → Prop} {Ctx : FragS isaLSE2} {lbl : Lbl} {lsize : Lsize}
  {R : Region} {F : MachineData → Prop} {ms : Spike.Lib.MemSide isaLSE2} {J1 : Spike.Lib.A64.Flow.AS → Ctl → Prop}
  {l : WeakMem.AllocLabel} {b : Nat} {ws : List TermRun.Word}
  (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)

set_option hygiene false in
/-- The root's third level at no frames. -/
local notation "W2" => fun s c => W2H L (ntA L.lab) ar Spike.Lib.HelloSrc.helloSrc Dt (Spike.Lib.A64.HelloPh.ClH L) Ctx lbl lsize s c []

include hp hlo hΛ hlab hsite

/-- **`wcWf_W2H` with the band from the region's base** (row 5f-wire): `hband` by `StackB.bandTiH_of` at
`R.base + 80` the first stack's top (`hbase`, `BoxPureH`'s). -/
theorem wcWf_W2Hb (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -336) (hhi : 0 ≤ R.hi)
    (hsepN : ntA L.lab ≠ L.pnA ∧ ntA L.lab ≠ L.lockA ∧ ntA L.lab ≠ L.freeNA ∧ ntA L.lab ≠ L.nextA)
    (hmN : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 L.Λ) true ⟨ntA L.lab, 8⟩ = true)
    (hunN : ∀ m, F m → Mem.loadInt m.dmem (ntA L.lab) 8 = none)
    (hb : Spike.Lib.A64.HelloPh.Tcb2CallW.BandSp3H L R)
    (hsep : L.pnA ≠ L.lockA ∧ L.pnA ≠ L.freeNA ∧ L.pnA ≠ L.nextA ∧ L.pnA ≠ ntA L.lab)
    (hhdr : L.pinA + 80#64 + 24#64 ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, ntA L.lab])
    (hmP : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 L.Λ) true ⟨L.pnA, 8⟩ = true)
    (hmH : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 L.Λ) true ⟨L.pinA + 104#64, 8⟩ = true)
    (hunP : ∀ m, F m → Mem.loadInt m.dmem L.pnA 8 = none)
    (hunH : ∀ m, F m → Mem.loadInt m.dmem (L.pinA + 104#64) 8 = none)
    (hbase : R.base.toNat + 80 = L.stacksA.toNat + 16384)
    (htidW : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 L.Λ) true ⟨tH L.lab + 56#64, 8⟩ = true ∧
      (∀ m', F m' → Mem.loadInt m'.dmem (tH L.lab + 56#64) 8 = none) ∧
      ∀ w, (⟨tH L.lab + 56#64, 8⟩, w) ∉ Spike.Lib.A64.HelloPh.own2aH L (ntA L.lab) 0)
    (hpl : WcMainWH (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F F ms J1
      (SBH l b ws) (QBH l b ws))
    (hoff56 : ¬ (ar.heap ≤ (tH L.lab + 56#64).toNat ∧ (tH L.lab + 56#64).toNat < ar.heap + 16 * ar.cells) ∧
      (⟨tH L.lab + 56#64, 8⟩ : Loc) ≠ ar.ctrLoc) :
    WcMainWH W2 (fun _ _ => False) L.exe L.endPc R F F ms J1 (SBH l b ws) (QBH l b ws) :=
  wcWf_W2H (Dt := Dt) (Ctx := Ctx) (lsize := lsize) hp hlo hΛ hlab hsite hR hal hRlo hhi hsepN hmN hunN hb hsep hhdr hmP hmH hunP hunH
    (Spike.Lib.A64.HelloPh.StackB.bandTiH_of hbase) htidW hpl hoff56

end Main

end Spike.Lib.A64.HelloPh.WcW2

namespace Spike.Lib.A64.Flow.Worker.Hello.SegR

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Worker
open Spike.Lib.A64.Flow.Worker.Hello.Child (Words wcJE childN pfxM)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Scc.Cert.Rt.A64 (Lays endOf)
open SccCode (helloProg)

open Kraken.Promising Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel Spike.Lib.Handover in
open Spike.Lib.HelloPreA (ClonePreH) in
open Spike.Lib.A64.Flow.Worker.Wake.Child (childR) in
/-- **`childP_of_clone` at the runtime's second stack** (row 5f-wire): `r1 := r1Of L.lab`, its bounds from its
place in the pool (`hsub`, `StackB.childB_r1Of`). -/
theorem childP_of_cloneR1 {lbl' : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
    (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
    (L : RuntimeLayout) (hsub : (Spike.Lib.A64.Rt.PreChild.r1Of L.lab).Sub L.Λ.stackPool)
    {Λ : Scc.Sem.Layout} {r0 : Scc.Sem.Range} {X : State → Prop} {lbl : WeakMem.AllocLabel → Option Nat}
    {t : Spike.Lib.WakeA64.Cfg} {s : TermRun.Cfg}
    (h : ClonePreH pfxM Λ r0 (Spike.Lib.A64.Rt.PreChild.r1Of L.lab) X lbl t s)
    (hX : ∀ st, X st → st.exe = exe ∧ st.endPc = endPc ∧ st.decls = {})
    (T : Ty) (w0 w1 w2 w3 w4 : TermRun.Word) (n m : Nat) :
    let top := (Spike.Lib.A64.Rt.PreChild.r1Of L.lab).lo + (Spike.Lib.A64.Rt.PreChild.r1Of L.lab).size
    ∃ (th : Thread isaLSE2) (tls sl0 sl1 sl2 sl3 cA meW : Nat), t.1.threads = #[th] ∧
      callOf abi th = some (.clone top tls) ∧
      (ChildPrem exe endPc kp lbl' ms
          (DFrame (childR top (-272)) (childAfter abi t.2 0 th top tls).st.st.1)
          ⟨BitVec.ofNat 64 sl0, BitVec.ofNat 64 sl1, BitVec.ofNat 64 sl2, BitVec.ofNat 64 sl3,
            BitVec.ofNat 64 cA, BitVec.ofNat 64 meW⟩
          (BitVec.ofNat 64 tls) (BitVec.ofNat 64 top) w0 w1 w2 w3 w4 n m →
        childP exe endPc kp lbl' ms (childAfter abi t.2 0 th top tls).st (kidH T w0 w1 w2 w3 w4) []) :=
  have hB := Spike.Lib.A64.HelloPh.StackB.childB_r1Of L hsub
  childP_of_clone (lbl' := lbl') (ms := ms) (kp := kp) hp hend h hX hB.1 hB.2.1 hB.2.2 T w0 w1 w2 w3 w4 n m

end Spike.Lib.A64.Flow.Worker.Hello.SegR

/-- info: 'Spike.Lib.A64.HelloPh.WcW2.wcWf_W2Hb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcW2.wcWf_W2Hb

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.SegR.childP_of_cloneR1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.SegR.childP_of_cloneR1
