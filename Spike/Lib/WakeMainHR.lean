/-
**wake.w on AArch64: `HMainR`, assembled**:
`hMainR_of`, `WakeSpawnR.HMainR` from the owners' pieces per witness tuple
(`MainPieces`), with `WakeMainR.mainWS_of` at the one-frame family
(`WakeMainFrames.frames_unit`, `γ := Unit`), whose flag-word premises are
`WakeMainFlag.hA0_of`/`hAoff_of` at `R1`'s private-memory invariant (`hpv`)
and `hat`'s `Abs`, and
`hsub` from `PreR.clone`.

`MainPieces` is what remains, at main's thread `th` after the clone, its
memory `m0` (`retThread` of `parentPre`), the record `g` and `cP = Ctl.of s0`:

- the segment end: `hhat`, `hRb`, `hRok`, `hal`, `htp`, `hra`;
- the source side: `htP`, `hlP`, `hwc`, `hval`, `hloc`, `hin`;
- `WakeMainInstD`: `hS`, `htls`, `hexit` at the frame
  `⟨Rm.base, -96, 16⟩`, the frame condition `DFrame` of it from `m0` and the
  frame pointer `x29`.

`locIn_cA` is the bridge from `GhOK` (`cT` shared) to `cA`'s word.
-/
import Spike.Lib.WakeMainR
import Spike.Lib.WakeMainFlag
import Spike.Lib.PlaceWRt

namespace Spike.Lib.WakeMainHR

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
open Spike.Lib.WakeSpawn (SpawnPrem)

/-- **The flag's word is shared**: `cA` the address `GhOK`'s `cS`
represents, as `WakeMainInst.hmA_I`. -/
theorem locIn_cA {Λ : Scc.Sem.Layout} {g : Gh} (hg : GhOK Λ g) {A : BitVec 64}
    (hv : ValRep g.lbl (.loc g.cS 0) A.toNat) : Spike.Lib.Consumer1.LocIn Λ.shared ⟨A, 8⟩ := by
  obtain ⟨-, -, -, ⟨b, hl, -, hT⟩, hsh⟩ := hg
  obtain ⟨-, x, hx, hAx⟩ := hv
  rw [show Scc.Sem.wordAddr g.lbl g.cS = some (b + 8 * g.cS.offset) by simp [Scc.Sem.wordAddr, hl]] at hx
  cases hx
  have hA' : A = BitVec.ofNat 64 (b + 8 * g.cS.offset) := by
    apply BitVec.eq_of_toNat_eq
    rw [hAx, BitVec.toNat_ofNat, Nat.add_zero, Nat.mod_eq_of_lt (by have := A.isLt; omega)]
  rw [hT] at hsh
  rw [hA']
  exact hsh

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- main's memory after the clone. -/
abbrev m0 (d : Cfg) (th : Thread isaLSE2) (r : BitVec 64) : MachineData :=
  (Kernel.retThread abi (parentPre abi d.2 0 th
    ((r1Of (RuntimeLayout.ofPlaceW hp i).lab).lo + (r1Of (RuntimeLayout.ofPlaceW hp i).lab).size)) r).st.st.1

/-- **The owners' pieces of `MainWS`** at one witness tuple (see the module
doc); `F` is the frame condition `DFrame ⟨Rm.base, -96, 16⟩ (m0 d th r)`. -/
structure MainPieces (g : Gh) (d : Cfg) (th : Thread isaLSE2) (r : BitVec 64) (cP c : Ctl) (Rm : Region)
    (F₂ : MachineData → Prop) (cA x29 ra tp : BitVec 64) (w : TermRun.Word) (tyP : Ty) : Prop where
  /- the segment end -/
  hhat : At (RuntimeLayout.ofPlaceW hp i).exe (endR hp i) ⟨Rm.base, -96, 16⟩ F₂
    ⟨cloneAt pfxM (RuntimeLayout.ofPlaceW hp i).exe, oP, JS c cA x29 ra tp⟩ th.st c
  hRb : (Rm.base.toNat : Int) = th.st.st.1.regs.SP.toNat + 80
  hRok : (⟨Rm.base, -96, 16⟩ : Region).OK
  hal : Rm.base.toNat % 16 = 0
  htp : tp = (RuntimeLayout.ofPlaceW hp i).pinA + 0#64 + 8#64
  hra : Int64.ofBitVec ra = (_root_.Executable.labels (RuntimeLayout.ofPlaceW hp i).exe).label mainSp0
  /- the source side -/
  htP : cP.term = mTail
  hlP : TermRun.lookupE cP.env "c" = some (tyP, [w])
  hwc : w.val = .loc g.cS 0
  hval : ValRep g.lbl w.val cA.toNat
  hloc : LocRep g.lbl w.val cA.toNat 0
  hin : ∃ sa, w.val = .loc sa 0 ∧ sa.offset < g.lsize sa.label
  /- `WakeMainInstD` -/
  hS : Ret0.StOk (wakeMs hp i g) (DFrame ⟨Rm.base, -96, 16⟩ (m0 hp i d th r)) (RuntimeLayout.ofPlaceW hp i).exe
    (endR hp i) (tp + 16#64) 0#64
  htls : SegW (mainWR (_root_.Executable.labels (RuntimeLayout.ofPlaceW hp i).exe).label
      (RuntimeLayout.ofPlaceW hp i).exe (RuntimeLayout.ofPlaceW hp i).Λ g.lbl g.lsize) (fun _ _ => False)
    Spike.Lib.WakeT1.wakeSrc g.lbl (wakeMs hp i g)
    (At (RuntimeLayout.ofPlaceW hp i).exe (endR hp i) ⟨Rm.base, -96, 16⟩ (DFrame ⟨Rm.base, -96, 16⟩ (m0 hp i d th r))
      (Spike.Lib.A64.WaitLoop.N (_root_.Executable.labels (RuntimeLayout.ofPlaceW hp i).exe).label
        Spike.Lib.A64.WakeLabels.pfx (waitC w) "d" wlIf (.ptr .pub .int)
        (fun w' => (wakeMs hp i g).rd w' ∧ ValRep g.lbl w'.val 1) cA x29 ra tp .tls))
    (At (RuntimeLayout.ofPlaceW hp i).exe (endR hp i) ⟨Rm.base, -96, 16⟩ (DFrame ⟨Rm.base, -96, 16⟩ (m0 hp i d th r))
      (Spike.Lib.A64.WaitLoop.N (_root_.Executable.labels (RuntimeLayout.ofPlaceW hp i).exe).label
        Spike.Lib.A64.WakeLabels.pfx (waitC w) "d" wlIf (.ptr .pub .int)
        (fun w' => (wakeMs hp i g).rd w' ∧ ValRep g.lbl w'.val 1) cA x29 ra tp .n1))
  hexit : ∀ s c', Spike.Lib.A64.WaitLoop.Past (waitC w) "d" wlIf (.ptr .pub .int)
    (fun w' => (wakeMs hp i g).rd w' ∧ ValRep g.lbl w'.val 1) c' →
    At (RuntimeLayout.ofPlaceW hp i).exe (endR hp i) ⟨Rm.base, -96, 16⟩ (DFrame ⟨Rm.base, -96, 16⟩ (m0 hp i d th r))
      ⟨(_root_.Executable.labels (RuntimeLayout.ofPlaceW hp i).exe).label mainSp0 + 4 + 4 + 4, ⟨0, []⟩,
        fun σ _ => σ.regs.X0.toBitVec = 0#64⟩ s c' →
    ¬ (wakeMs hp i g).abortAt s → MainExit Spike.Lib.WakeT1.wakeSrc (wakeMs hp i g) s c' 0

/-- **`HMainR` from the owners' pieces** (see the module doc). -/
theorem hMainR_of {asm : String} {E : Entry} {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {μ : Marks}
    {M : WakeM0.MSide (ιR hp i)} {r0 r1 : ιR hp i → Range}
    (hw : Scc.Cert.WideA64.ExeWide (RuntimeLayout.ofPlaceW hp i).exe)
    (hpv : ∀ d s, R1 d s → ∃ (Ent : Entry) (P : State → Prop), Ent.clear (RuntimeLayout.ofPlaceW hp i).Λ = true ∧
      Spike.Lib.DmemPriv.PrivInv abi P (RuntimeLayout.ofPlaceW hp i).Λ Ent d)
    (hpc : ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q,
      SpawnPrem (QG hp i arch R1 μ M r0 r1) (RuntimeLayout.ofPlaceW hp i).Λ asm E 0 d s th stack tls r →
      (wakeS arch).Run s [] s' →
      PreR hp i arch R1 μ M r0 r1 d th stack s s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q →
      ∃ c Rm F₂ cA x29 ra tp cw tyP,
        MainPieces hp i w.1 d th r (Ctl.of s0) c Rm F₂ cA x29 ra tp cw tyP) :
    HMainR hp i asm E arch R1 μ M r0 r1 := by
  intro d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q hP hrun hR
  obtain ⟨c, Rm, F₂, cA, x29, ra, tp, cw, tyP, hM⟩ := hpc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hP hrun hR
  have hg := w.2
  have hth := hR.pre.threads
  have hth0 : d.1.threads[0]? = some th := by rw [hth]; rfl
  obtain ⟨_thc, -, _tlsc, -, -, -, _hthc, -, -, -, -, _hcall, -, _h3c, -, -, _hheld, -, -, hO1, _hXc, -⟩ := hR.clone
  obtain ⟨Ent, P, hE, hc⟩ := hpv d s hP.1
  have hwf : (RuntimeLayout.ofPlaceW hp i).Λ.WF := PlaceW.wf_link_of_placeW i hp
  have hA := locIn_cA hg (hM.hwc ▸ hM.hval)
  obtain ⟨-, -, -, -, σ, hAbs, -, -⟩ := hM.hhat
  have hoff := WakeMainFlag.hAoff_of hc hE hwf hth0 hM.hRok (show (-96 : Int) % 8 = 0 by decide)
    (show (16 : Int) % 8 = 0 by decide) (show (-96 : Int) < 16 by decide) hAbs hA
  obtain ⟨hRg, hfp, hFg, hF, hRo, hal, hlo, hhi, hdm⟩ := WakeMainFrames.frames_unit (x29 := x29)
    (m0 := m0 hp i d th r) hM.hRok hM.hal (WakeMainFlag.hA0_of hc hE hwf hth0 hA _ r) hoff.1 hoff.2
  have elbl : w.val.lbl = lbl := by rw [hR.hw]; rfl
  have elsz : w.val.lsize = lsize := by rw [hR.hw]; rfl
  rw [← elbl, ← elsz]
  exact ⟨Ctl.of s0, ⟨Rm.base, -96, 16⟩, F₂, cA, x29, ra, tp, cw, tyP, Unit, fun _ => ⟨Rm.base, -96, 16⟩,
    fun _ => DFrame ⟨Rm.base, -96, 16⟩ (m0 hp i d th r), fun _ => x29, (), rfl,
    WakeMainR.mainWS_of hp i hg hth hM.hhat hM.hRb hM.hRok hM.htp hM.hra (γ := Unit)
      (Rg := fun _ => ⟨Rm.base, -96, 16⟩) (Fg := fun _ => DFrame ⟨Rm.base, -96, 16⟩ (m0 hp i d th r))
      (fp := fun _ => x29) (g0 := ()) hRg hfp hFg hF hRo hal hlo hhi hdm hO1.1
      hM.htP hM.hlP hM.hwc hM.hval hM.hloc hM.hin (fun _ => hM.hS) (fun _ => hM.htls) (fun _ => hM.hexit) hw⟩

end Inst

/-- info: 'Spike.Lib.WakeMainHR.locIn_cA' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms locIn_cA

/-- info: 'Spike.Lib.WakeMainHR.hMainR_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hMainR_of

end Spike.Lib.WakeMainHR
