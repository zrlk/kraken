/-
**wake.w on AArch64: main's facts past the clone, composed**: `mainWS_of`, `WakeSpawnR.MainWS` at the instance (the
layout `L := RuntimeLayout.ofPlaceW hp i`, the record `g` with `GhOK`, its
memory side `wakeMs`, the child's range `r1Of`) from its pieces, each a
named hypothesis in the form its owner delivers:

- the segment end (`A64WakeWcHat.wake_wc_mid_hatW`'s post at main's
  thread `th`): `hhat` (at the source control `c` of the segment; moved to
  `cP` here, `JS` only pins the control), `hRb`, `hRok` (the region
  `⟨Rm.base, -96, 16⟩`'s `OK`), `htp` (main's TCB, from `J0`), `hra` (from
  `FrG J0 fr`), the frame family `Rg`, `Fg`, `fp`, `g0` with `hRg`, `hfp`,
  `hFg`, `hF`, `hRo`, `hal`, `hlo`, `hhi`, `hdm`;
- the source side at `cP = Ctl.of s0`: `htP`, `hlP`, `hval`, `hloc`,
  `hin`, `hwc` (`c`'s word the record's flag word);
- `WakeMainInstD`: `hS`, `htls`, `hexit`;
- `WakeMainInst`: `htop`, `htp4`, `hwide`, `hmA`, `hmP`, `hmE`
  (here from `hsub`, `htp`, `hw`, `hg` and the source pieces).

`HMainR` is `mainWS_of` per witness tuple once the pieces are (`PreR`
fields or lemmas over `SpawnPrem`, the run and `PreR`).

`hhat` is at `endR = endOf L.exe wakeProg L.pfx`, the instance's prefix
(`wake_wc_mid_hatW` is generic in it).
-/
import Spike.Lib.WakeMainInst
import Spike.Lib.PlaceWRt

namespace Spike.Lib.WakeMainR

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib.A64.Flow
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.Handover Spike.Lib.WakeSpawnR
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.Rt.PreChild (r1Of)
open Spike.Lib.WakeInst (Gh wakeMs mainWR)
open Spike.Lib.WakeInstFields (GhOK)
open Spike.Lib.WakePreA (cloneAt)
open Spike.Lib.A64.Flow.Worker.Wake.Child (pfxM)
open Spike.Lib.A64.Flow.Worker.Wake.Parent (JS oP)
open Spike.Lib.A64.Flow.Worker.Wake.MainPost (mainSp0)
open Spike.Lib.WakeMainSrc (waitC)
open Spike.Lib.WakeM0 (mTail wlIf)

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- **`MainWS` at the instance from its pieces** (see the module doc). -/
theorem mainWS_of {g : Gh} (hg : GhOK (RuntimeLayout.ofPlaceW hp i).Λ g) {d : Cfg} {th : Thread isaLSE2}
    (hth : d.1.threads = #[th]) {r : BitVec 64}
    /- the segment end at `th` -/
    {c : Ctl} {Rm : Region} {F₂ : MachineData → Prop} {cA x29 ra tp : BitVec 64}
    (hhat : At (RuntimeLayout.ofPlaceW hp i).exe (endR hp i) ⟨Rm.base, -96, 16⟩ F₂
      ⟨cloneAt pfxM (RuntimeLayout.ofPlaceW hp i).exe, oP, JS c cA x29 ra tp⟩ th.st c)
    (hRb : (Rm.base.toNat : Int) = th.st.st.1.regs.SP.toNat + 80)
    (hRok : (⟨Rm.base, -96, 16⟩ : Region).OK)
    (htp : tp = (RuntimeLayout.ofPlaceW hp i).pinA + 0#64 + 8#64)
    (hra : Int64.ofBitVec ra = (_root_.Executable.labels (RuntimeLayout.ofPlaceW hp i).exe).label mainSp0)
    {γ : Type} {Rg : γ → Region} {Fg : γ → MachineData → Prop} {fp : γ → BitVec 64} {g0 : γ}
    (hRg : Rg g0 = ⟨Rm.base, -96, 16⟩) (hfp : fp g0 = x29)
    (hFg : ∀ m, DFrame ⟨Rm.base, -96, 16⟩ (Kernel.retThread abi (parentPre abi d.2 0 th
      ((r1Of (RuntimeLayout.ofPlaceW hp i).lab).lo + (r1Of (RuntimeLayout.ofPlaceW hp i).lab).size)) r).st.st.1 m →
      Fg g0 m)
    (hF : ∀ g', FStable (Rg g') (Fg g')) (hRo : ∀ g', (Rg g').OK) (hal : ∀ g', (Rg g').base.toNat % 16 = 0)
    (hlo : ∀ g', (Rg g').lo ≤ -96) (hhi : ∀ g', 16 ≤ (Rg g').hi) (hdm : ∀ g' m, Fg g' m → Mem.loadInt m.dmem cA 8 = none)
    /- the clone: the child's range in the pool -/
    (hsub : (r1Of (RuntimeLayout.ofPlaceW hp i).lab).Sub (RuntimeLayout.ofPlaceW hp i).Λ.stackPool)
    /- the source side at `cP` -/
    {cP : Ctl} {w : TermRun.Word} {tyP : Ty} (htP : cP.term = mTail)
    (hlP : TermRun.lookupE cP.env "c" = some (tyP, [w])) (hwc : w.val = .loc g.cS 0)
    (hval : ValRep g.lbl w.val cA.toNat) (hloc : LocRep g.lbl w.val cA.toNat 0)
    (hin : ∃ sa, w.val = .loc sa 0 ∧ sa.offset < g.lsize sa.label)
    /- the runtime word, the TLS check and the exit -/
    (hS : ∀ g', Ret0.StOk (wakeMs hp i g) (Fg g') (RuntimeLayout.ofPlaceW hp i).exe (endR hp i) (tp + 16#64) 0#64)
    (htls : ∀ g',
      SegW (mainWR (_root_.Executable.labels (RuntimeLayout.ofPlaceW hp i).exe).label
          (RuntimeLayout.ofPlaceW hp i).exe (RuntimeLayout.ofPlaceW hp i).Λ g.lbl g.lsize) (fun _ _ => False)
        Spike.Lib.WakeT1.wakeSrc g.lbl (wakeMs hp i g)
        (At (RuntimeLayout.ofPlaceW hp i).exe (endR hp i) (Rg g') (Fg g')
          (Spike.Lib.A64.WaitLoop.N (_root_.Executable.labels (RuntimeLayout.ofPlaceW hp i).exe).label
            Spike.Lib.A64.WakeLabels.pfx (waitC w) "d" wlIf (.ptr .pub .int)
            (fun w' => (wakeMs hp i g).rd w' ∧ ValRep g.lbl w'.val 1) cA (fp g') ra tp .tls))
        (At (RuntimeLayout.ofPlaceW hp i).exe (endR hp i) (Rg g') (Fg g')
          (Spike.Lib.A64.WaitLoop.N (_root_.Executable.labels (RuntimeLayout.ofPlaceW hp i).exe).label
            Spike.Lib.A64.WakeLabels.pfx (waitC w) "d" wlIf (.ptr .pub .int)
            (fun w' => (wakeMs hp i g).rd w' ∧ ValRep g.lbl w'.val 1) cA (fp g') ra tp .n1)))
    (hexit : ∀ g' s c', Spike.Lib.A64.WaitLoop.Past (waitC w) "d" wlIf (.ptr .pub .int)
      (fun w' => (wakeMs hp i g).rd w' ∧ ValRep g.lbl w'.val 1) c' →
      At (RuntimeLayout.ofPlaceW hp i).exe (endR hp i) (Rg g') (Fg g')
        ⟨(_root_.Executable.labels (RuntimeLayout.ofPlaceW hp i).exe).label mainSp0 + 4 + 4 + 4, ⟨0, []⟩,
          fun σ _ => σ.regs.X0.toBitVec = 0#64⟩ s c' →
      ¬ (wakeMs hp i g).abortAt s → MainExit Spike.Lib.WakeT1.wakeSrc (wakeMs hp i g) s c' 0)
    /- the instance -/
    (hw : Scc.Cert.WideA64.ExeWide (RuntimeLayout.ofPlaceW hp i).exe) :
    MainWS (RuntimeLayout.ofPlaceW hp i).exe (endR hp i) (RuntimeLayout.ofPlaceW hp i).Λ g.lbl g.lsize
      (wakeMs hp i g) d (r1Of (RuntimeLayout.ofPlaceW hp i).lab) r cP ⟨Rm.base, -96, 16⟩ F₂ cA x29 ra tp w tyP
      Rg Fg fp g0 where
  hat th' hth' := by
    rw [hth] at hth'
    cases (List.singleton_inj.mp (congrArg Array.toList hth'))
    obtain ⟨h1, h2, h3, h4, σ, hA, hF0, -, hJ⟩ := hhat
    exact ⟨h1, h2, h3, h4, σ, hA, hF0, rfl, hJ⟩
  hRb th' hth' := by
    rw [hth] at hth'
    cases (List.singleton_inj.mp (congrArg Array.toList hth'))
    exact hRb
  hRlo := rfl
  hRhi := rfl
  hR := hRok
  htop := WakeMainInst.htop_I hp i hsub
  htP := htP
  hlP := hlP
  hval := hval
  hloc := hloc
  hin := hin
  hRg := hRg
  hfp := hfp
  hFg th' hth' := by
    rw [hth] at hth'
    cases (List.singleton_inj.mp (congrArg Array.toList hth'))
    exact hFg
  hF := hF
  hRo := hRo
  hal := hal
  hlo := hlo
  hhi := hhi
  hdm := hdm
  hS := hS
  htp4 := WakeMainInst.htp4_I hp i htp
  htls := htls
  hra := hra
  hexit := hexit
  hwide := WakeMainInst.hwide_I hp i hw
  hmA := WakeMainInst.hmA_I hg (hwc ▸ hval)
  hmP := WakeMainInst.hmP_I htP
  hmE := WakeMainInst.hmE_I

end Inst

/-- info: 'Spike.Lib.WakeMainR.mainWS_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainWS_of

end Spike.Lib.WakeMainR
