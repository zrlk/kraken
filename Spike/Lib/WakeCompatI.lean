/-
**The worker's compatibility facts at the instance** (AArch64): `WakeAssemblyI.wake_obligations_IWW`'s `hC` (`WCompat`) and `hx`
(`WCompatX`) at the worker's side `D := WakeWorkerX.wakeD` and the instance's
relation data (`WakeInst.wakeQI`'s: spawn records `wakeSR ·.1`, flag words
`·.1.cT`/`·.1.cS`, `P := wakeP abi μ (wakeLocs hp i ·.1)`,
`G := wakeG' hp i ·.1`), for any main side `M`. The listing is wake.w's
certificate (`Spike/Test/Cert/A64WakeCert.s`).

- `hx_I`: `WCompatX`, closed (`Gc` by `WakeG.wakeG_cT`, the rest by
  `WakeAssembly.wCompatX_of`).
- `hC_I`: `WCompat` by `WakeAssembly.wCompat_of`, the fields by
  `WorkerSide.sideF_ofXv`, `G`/`own`/`mpW`/`C`/`cTfoot`/`cSfrz`/`footLab`/
  `noProm` from the instance's definitions. Open: `hμ` (the marks' sites,
  `WorkerSide.wake_hμ` at the loader's parse), the worker's pointer word
  `hcw` (`w.1.cwW.val` the flag's untagged locative; `WakeOkW.okW_hcw`), and
  the main-side placement fields `cT`, `cTin`, `Spos`.
- `hflag_of`: `WakeChildXI.childSeg_XI`'s `hflag` from those `cT`, `cTin`.
- `hC_okW`: `hC_I` at `ok := WakeOkW.okW` (the placement's layout), `hcw`,
  `cT`, `cTin`, `Spos` from the records' `okW`; open only `hμ`.
-/
import Spike.Lib.WakeWorkerX
import Spike.Lib.WakeAssembly
import Spike.Lib.WakeSideFieldsX
import Spike.Lib.WakeOkW
import Spike.Lib.PlaceWRt

namespace Spike.Lib.WakeCompatI

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeT1 Spike.Lib.WakeW1 Spike.Lib.WakeP
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.WakeInst (Gh wakeMs wakeSR wakeG' wakeLocs)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Scc.Cert.Rt.A64 (Lays endOf)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (ok : Gh → Prop) (exe : _root_.Executable) (endPc : Int64) (kp : Nat)
  (lbl' : WeakMem.AllocLabel → Option Nat) (cSf : WeakMem.Address)
  {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {μ : Marks} {M : WakeM0.MSide {g : Gh // ok g}}
  {r0 r1 : {g : Gh // ok g} → Range}

/-- **The instance's relation at the worker's side `wakeD`** (`wakeQI`'s
data, main side `M`, marks `μ`). -/
noncomputable abbrev QI (arch : WeakMem.Arch) (R1 : Cfg → TermRun.Cfg → Prop) (μ : Marks)
    (M : WakeM0.MSide {g : Gh // ok g}) (r0 r1 : {g : Gh // ok g} → Range) : WakeRel :=
  WakeQ.wakeQ arch R1 {g : Gh // ok g} (wakeSR ·.1) (·.1.cT) (·.1.cS) (·.1.pT)
    (fun g => wakeP abi μ (wakeLocs hp i g.1)) (fun g => wakeG' hp i g.1) M
    (WakeWorkerX.wakeD hp i ok exe endPc kp lbl' cSf) r0 r1

/-- **`wake_obligations_IWW`'s `hx`** at the instance: closed. -/
theorem hx_I :
    WCompatX (QI hp i ok exe endPc kp lbl' cSf arch R1 μ M r0 r1) (WakeWorkerX.wakeD hp i ok exe endPc kp lbl' cSf) :=
  WakeAssembly.wCompatX_of WakeQ.hPT0 WakeQ.hKR WakeQ.hown fun _ => WakeG.wakeG_cT (G0 := _) _

/-- **`wake_obligations_IWW`'s `hC`** at the instance: `wCompat_of` with
the fields (`sideF_ofXv`) and the instance's definitional fields; open
`hμ`, `hcw` and `cT`, `cTin`, `Spos`. -/
theorem hC_I [Kraken.Executable.ValidLayout exe] (hl : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp)
    (hμ : μ.site .take = some ((_root_.Executable.labels exe).label Scc.Lower.Names.takeSite).toBitVec.toNat ∧
      μ.site .release = some ((_root_.Executable.labels exe).label Scc.Lower.Names.releaseSite).toBitVec.toNat)
    /- (the record, `WakeOkW.okW_hcw`) the worker's pointer word's value is the
    flag's untagged locative -/
    (hcw : ∀ w : {g : Gh // ok g}, w.1.cwW.val = .loc w.1.cS 0)
    /- OPEN: the flag's word placed at the spawn, shared; the source
    memory not empty -/
    (cT : ∀ w : {g : Gh // ok g}, ∃ a, w.1.cT = wordLoc a ∧ wordAddr w.1.lbl w.1.cS = some a ∧
      w.1.cS.offset < w.1.lsize w.1.cS.label)
    (cTin : ∀ w : {g : Gh // ok g}, Consumer1.LocIn (RuntimeLayout.ofPlaceW hp i).Λ.shared w.1.cT)
    (Spos : ∀ w : {g : Gh // ok g}, 0 < w.1.S) :
    WCompat (QI hp i ok exe endPc kp lbl' cSf arch R1 μ M r0 r1) (WakeWorkerX.wakeD hp i ok exe endPc kp lbl' cSf)
      μ (RuntimeLayout.ofPlaceW hp i).Λ arch :=
  WakeAssembly.wCompat_of WakeQ.hPT0 WakeQ.hKR WakeQ.hown WakeQ.pt1 WakeQ.atUnpk WakeQ.atTexit
    (WorkerSide.sideF_ofXv hl hend hμ (fun _ => rfl) hcw (fun _ => rfl))
    (fun _ => rfl) (fun _ _ => rfl)
    (fun w L hm => ⟨Or.inr (Or.inl hm), (hm.2 rfl).2, (hm.2 rfl).1⟩)
    WakeQ.hC cT cTin (fun _ => Or.inr (Or.inr ⟨rfl, rfl⟩)) (fun _ h => h.2 rfl) Spos
    (fun w L hf hL => by
      rcases hf with hf | hf | ⟨-, hf⟩
      · exact hf.elim
      · exact ((WakeInst.wakeLocs_ok hp i w.1).priv_nlab 1 L (by omega) hf hL).elim
      · exact hf)
    WakeQ.hpT (fun _ _ _ _ hn hc => noProm_prom hn hc)

/-- **`WakeChildXI.childSeg_XI`'s `hflag`** from `hC_I`'s `cT`/`cTin` at a
record whose flag is `cSf`. -/
theorem hflag_of {g : Gh} (hcS : g.cS = cSf)
    (cT : ∃ a, g.cT = wordLoc a ∧ wordAddr g.lbl g.cS = some a ∧ g.cS.offset < g.lsize g.cS.label)
    (cTin : Consumer1.LocIn (RuntimeLayout.ofPlaceW hp i).Λ.shared g.cT) :
    ∀ x, wordAddr g.lbl cSf = some x → Consumer1.LocIn (RuntimeLayout.ofPlaceW hp i).Λ.shared (wordLoc x) := by
  obtain ⟨a, hT, hA, -⟩ := cT
  intro x hx
  rw [← hcS, hA] at hx
  cases hx
  rw [← hT]; exact cTin

/-- **`hC_I` at wake.w's records' facts** `okW`: every premise but the
marks' sites `hμ` from `okW` (`WakeOkW.okW_hcw`, `okW_cT`, `okW_cTin`,
`okW_Spos`). -/
theorem hC_okW [Kraken.Executable.ValidLayout exe] (hl : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp)
    (hμ : μ.site .take = some ((_root_.Executable.labels exe).label Scc.Lower.Names.takeSite).toBitVec.toNat ∧
      μ.site .release = some ((_root_.Executable.labels exe).label Scc.Lower.Names.releaseSite).toBitVec.toNat)
    {M : WakeM0.MSide {g : Gh // WakeOkW.okW (RuntimeLayout.ofPlaceW hp i).Λ lbl' cSf g}}
    {r0 r1 : {g : Gh // WakeOkW.okW (RuntimeLayout.ofPlaceW hp i).Λ lbl' cSf g} → Range} :
    WCompat (QI hp i (WakeOkW.okW (RuntimeLayout.ofPlaceW hp i).Λ lbl' cSf) exe endPc kp lbl' cSf arch R1 μ M r0 r1)
      (WakeWorkerX.wakeD hp i (WakeOkW.okW (RuntimeLayout.ofPlaceW hp i).Λ lbl' cSf) exe endPc kp lbl' cSf)
      μ (RuntimeLayout.ofPlaceW hp i).Λ arch :=
  hC_I hp i _ exe endPc kp lbl' cSf hl hend hμ (fun w => WakeOkW.okW_hcw w) (fun w => WakeOkW.okW_cT w)
    (fun w => WakeOkW.okW_cTin w) (fun w => WakeOkW.okW_Spos w)

/-- info: 'Spike.Lib.WakeCompatI.hC_okW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hC_okW

/-- info: 'Spike.Lib.WakeCompatI.hx_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hx_I

/-- info: 'Spike.Lib.WakeCompatI.hC_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hC_I

end Spike.Lib.WakeCompatI
