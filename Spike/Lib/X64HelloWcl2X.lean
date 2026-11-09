/-
**hello.w's `wc_main` at its `clone`'s `syscall` at `ownGHXW`** (x86-64 only; the hello counterpart of
`Spike/Lib/X64WakeWcl.lean`'s lift to `ownGXW`): `Wcl2.wcl_W2H`'s level `W2H` at `ownGH` moved to `W2HX`, the same
level at main's pre-spawn map with both TCB self words (`ownGHXW = ownGH ++ ownSH ++ ownSWH`, `X64HelloOwnSX`).

The `syscall` (`WcSp6.wcNSH`, `.Lwc_main.x3 + 94`) and its resumption (`+ 96`) are in `InCH` (`wc_main`'s `.x25`
to `.stk`), so with `wc_main`'s frame on the pool (`hb : BandOnP L R (-144) 8`, its `%rsp` at the frame's `-128`)
both words are held there (`cls_poolWH`); the `syscall` writes nothing, so `CstOkH` holds at the node
(`nodeW_cstOkHK`) and `Wf.appendS` twice lifts the level.

- `W2HX`: `W2H` at `ownGHXW` (`RootWX.W2Hg`).
- `w2HX_of`: `W2H` where `CstOkH` is `W2HX`.
- `cstOk_wcNSH`: `CstOkH` at every state of `wcNSH`.
- `wcl_W2HX`: `wcl_W2H` at `W2HX`.
- `wcl_W2GJ1HX`: the same at a ghost of `GJ1H`.

## Differences from the AArch64 version

AArch64 has no counterpart (main owns no TCB word there). Against x86-64 wake's `wcl_W1`: wake lifts the state
facts by `nodeL2` inside its proof (class `QW`, band `[-80, 8]`); here the existing `wcl_W2H` is reused and lifted
from outside (`CstOkH` by `nodeW_cstOkHK`, class `InCH` itself, band `[-144, 8]` for hello's 128-byte frame), and
the separations (`hs`, `ha`, `hW`) are premises, `wcl_W2H`'s layout being generic.
-/
import Spike.Lib.X64HelloWcl2
import Spike.Lib.X64HelloOwnCstX
import Spike.Lib.X64WakeOwnWfApp

namespace Spike.Lib.X64.HelloPh.Wcl2X

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (codeLabel pcOf abi)
open SccCode (helloCells)
open Spike.Lib (Arena FragS Ctl Region)
open Spike.Lib.X64 (At)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.Rt.Reserve (ntA)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64ConsumerS (PlacedSE)
open Spike.Lib.X64.Flow.WakeWc (MidG)
open Spike.Lib.X64.Flow.HelloWc (FrMGH)
open Spike.Lib.X64.HelloPh.WcSp6 (wcNSH x25L)
open Spike.Lib.X64.HelloPh.RootWX (W2H)
open Spike.Lib.X64.HelloPh.Ti2 (SlotPH SlotSlH)
open Spike.Lib.X64.Rt.PreChild (r1Of)
open Spike.Lib.X64.Flow.Ret0 (StackM)
open Spike.Lib.X64HelloHMid (SBH slWsH)
open Spike.Lib.X64HelloMainPreSrc (SpawnSrcH)
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.X64.WakePh (tcbM BandOnP keep_pc keep_syscall)
open Spike.Lib.X64.HelloPh (ownGHXW CstOkH InCH InAbH InTH)
open Spike.Lib.X64HelloOwnLift (tcbWH)

/-- **The root's third level at `ownGHXW`**: `W2H` with main's and the worker's TCB words appended
(`RootWX.W2Hg` at `ownGHXW`). -/
abbrev W2HX (L : RuntimeLayout) (a : BitVec 64) (ar : Arena) (p : Prog) (Dt Cl : State → Prop) (Ctx : FragS isa)
    (lbl : Lbl) (lsize : Lsize) : FragS isa :=
  Spike.Lib.X64.HelloPh.RootWX.W2Hg (ownGHXW L a) L ar p Dt Cl Ctx lbl lsize

variable {L : RuntimeLayout}

/-- **`W2H` where both words may be appended is `W2HX`** (`Wf.appendS` twice). -/
theorem w2HX_of {a : BitVec 64} {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isa} {lbl : Lbl}
    {lsize : Lsize} {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (h : W2H L a ar p Dt Cl Ctx lbl lsize s c fs) (hc : CstOkH (Spike.Lib.X64.PhRec.μ L) L a s) :
    W2HX L a ar p Dt Cl Ctx lbl lsize s c fs :=
  ⟨h.1, (h.2.appendS hc.1).appendS hc.2⟩

section Wcl

variable {ar : Arena} {Dt : State → Prop} {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize} {R : Region}
  {F : MachineData → Prop} {J1 : Spike.Lib.X64.AS → Ctl → Prop} {l : WeakMem.AllocLabel} {b : Nat}
  {ws : List TermRun.Word}
  (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = Spike.Lib.X64.HelloPh.lo)
  (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeLabel Spike.Lib.X64.HelloPh.lo helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hs : Spike.Lib.X64.PhRec.TcbSep L) (ha : tcbM L ≠ ntA L.lab)
  (hW : tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, ntA L.lab])
  (hb : BandOnP L R (-144) 8)

include hp hlab hs ha hW hb in
/-- **`CstOkH` at the clone's `syscall`**: its pc and the resumption's in `InCH` (not `InAbH`), `%rsp` at the
frame's `-128` on the pool (`cls_poolWH`), the successors keeping `%rsp` (`keep_syscall`), no write. -/
theorem cstOk_wcNSH {c0 : Ctl} {t k : BitVec 64} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64}
    {me cA : BitVec 64} {fr : BitVec 64 × BitVec 64} :
    ∀ s c, At L.exe L.endPc R F (wcNSH (_root_.Executable.labels L.exe).label c0 t k sl me cA fr) s c →
      CstOkH (Spike.Lib.X64.PhRec.μ L) L (ntA L.lab) s := by
  have e25 : L.lab x25L = Int64.ofNat 4203812 := Spike.Lib.X64.HelloPh.WcSp4W.lab_x25H hlab
  intro s c hA
  refine Spike.Lib.X64.HelloPh.nodeW_cstOkHK hs ha hW (sz := 2)
    (P := fun p => (InTH p ∨ InCH p) ∧ ¬ InAbH p) (Spike.Lib.X64.HelloPh.cls_poolWH hlab hb)
    (fun s c h s' hs' => ?_) ?_ (by dsimp only [wcNSH]; decide) ?_ s c hA |>.1
  · have hc := (Spike.Lib.X64.HelloPh.Wcl2.svc_clH hp h).1
    have hK := keep_syscall (Scc.Sem.X64.atSyscall_of_cellAt hc) hs'
    exact ⟨hK, by rw [keep_pc hc hK, h.2.2.2.1]⟩
  · show (_ ∧ _) ∧ (_ ∧ _)
    simp only [wcNSH]
    rw [show (_root_.Executable.labels L.exe).label x25L = Int64.ofNat 4203812 from e25]
    decide +kernel
  · intro s c h hns
    exact absurd ((Scc.Sem.X64.atSyscall_of_cellAt (Spike.Lib.X64.HelloPh.Wcl2.svc_clH hp h).1).symm.trans hns)
      (by decide)

include hp hlo hΛ hlab hsite hs ha hW hb

set_option maxHeartbeats 1600000 in
/-- **`H1GAHX.wcl` at `W2HX`**: `Wcl2.wcl_W2H` lifted by `cstOk_wcNSH`. -/
theorem wcl_W2HX (hRlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (Hs : ∀ c0 sl me cA fr, MidG (SBH l b ws) c0 cA ∧ FrMGH J1 fr sl me → ∀ s : State,
      SlotPH R b me.toNat s.st.1 ∧ SlotSlH R sl.1.toNat sl.2.2.1.toNat sl.2.2.2.toNat s.st.1 →
      PlacedSE L.Λ lbl s c0 [])
    {t k : BitVec 64} :
    ∀ s c sl me cA fr, At L.exe L.endPc R F (wcNSH L.lab c t k sl me cA fr) s c →
      SpawnSrcH l ws c → cA.toNat = b → FrMGH J1 fr sl me → StackM (r1Of L.lab) s.st.1 →
      W2HX L (ntA L.lab) ar helloSrc Dt (Spike.Lib.X64.HelloPh.ClH L) Ctx lbl lsize s c [] ∧
        StackM (r1Of L.lab) s.st.1 := by
  intro s c sl me cA fr hA hsrc hcA hFr hSM
  have h := Spike.Lib.X64.HelloPh.Wcl2.wcl_W2H (ar := ar) (Dt := Dt) (Ctx := Ctx) (lbl := lbl)
    (lsize := lsize) hp hlo hΛ hlab hsite hRlo hhi Hs
    s c sl me cA fr hA hsrc hcA hFr hSM
  exact ⟨w2HX_of h.1 (cstOk_wcNSH hp hlab hs ha hW hb s c hA), h.2⟩

/-- **`H1GAHX.wcl` at a ghost of `GJ1H`, at `W2HX`** (`Wcl2.wcl_W2GJ1H`'s placement). -/
theorem wcl_W2GJ1HX (hRlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) {lbl1 : Lbl} {lr l' : WeakMem.AllocLabel} {b' : Nat}
    {F' : MachineData → Prop} {tp : UInt64} (hl' : lbl1 l' = none)
    (hmt : lbl1 (Spike.Lib.X64WakeSrcDefs.mainTidLbl 2) = some (L.pinA.toNat + 8))
    (hG : Spike.Lib.X64HelloH2G.GJ1H L lbl1 lr R F' J1 tp) {t k : BitVec 64} :
    ∀ s c sl me cA fr, At L.exe L.endPc R F (wcNSH L.lab c t k sl me cA fr) s c →
      SpawnSrcH l' (slWsH lr) c → cA.toNat = b' → FrMGH J1 fr sl me → StackM (r1Of L.lab) s.st.1 →
      W2HX L (ntA L.lab) ar helloSrc Dt (Spike.Lib.X64.HelloPh.ClH L) Ctx (Spike.Lib.X64ConsumerA.upd lbl1 l' b')
        lsize s c [] ∧ StackM (r1Of L.lab) s.st.1 :=
  wcl_W2HX hp hlo hΛ hlab hsite hs ha hW hb hRlo hhi (Spike.Lib.X64.HelloPh.SpawnPl.hpl_GJ1H hl' hmt hG)

end Wcl

end Spike.Lib.X64.HelloPh.Wcl2X

/-! ## Axioms -/

/-- info: 'Spike.Lib.X64.HelloPh.Wcl2X.w2HX_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Wcl2X.w2HX_of

/-- info: 'Spike.Lib.X64.HelloPh.Wcl2X.cstOk_wcNSH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Wcl2X.cstOk_wcNSH

/-- info: 'Spike.Lib.X64.HelloPh.Wcl2X.wcl_W2HX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Wcl2X.wcl_W2HX

/-- info: 'Spike.Lib.X64.HelloPh.Wcl2X.wcl_W2GJ1HX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Wcl2X.wcl_W2GJ1HX
