/-
**`HMainR` from the segment end alone** (wake.w, AArch64): the source
fields (`WakeMainSrcR.src_pieces_R`) and the (`WakeMainInstD.hS_I`,
`htls_I`, `hexit_I`) supplied inside, so that the open premise `hpc` carries
only the segment-end fields (`MainSeg`), `hA` and `hZ`.

- `MainSeg`: `MainPieces`' segment-end fields (`hhat`, `hRb`, `hRok`, `hal`,
  `htp`, `hra`).
- `hMainR_ofD`: `WakeMainHR.hMainR_of` with `cP = Ctl.of s0`, `c`'s word
  `cst (.loc ⟨l,0⟩ 0)` at `.ptr .pub .int`. Inside: the source fields from
  `PreR` (`hc`, `hin`, `hw`, `hsp`) and `hA`; `hm` from `PreR.pre.inv1.mem`;
  `hA0`/`hoff` for `tp + 16` and `tp + 8` by `WakeMainFlag.hA0_of`/`hAoff_of`
  at `locIn_tp16_I`/`locIn_tp8_I` (the private invariant from `hpv`, the
  frame from `hhat`'s `Abs`). Open: `hprog` (the instance), `hw`, `hpv`,
  and `hpc`'s `MainSeg`, `hA : lbl l = some cA.toNat`, `hZ`.
-/
import Spike.Lib.WakeMainInstD
import Spike.Lib.WakeMainSrcR
import Spike.Lib.PlaceWRt

namespace Spike.Lib.WakeMainHRD

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib.A64.Flow
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.Handover Spike.Lib.WakeSpawnR
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.WakeInst (Gh wakeMs mainWR)
open Spike.Lib.WakePreA (cloneAt)
open Spike.Lib.A64.Flow.Worker.Wake.Child (pfxM)
open Spike.Lib.A64.Flow.Worker.Wake.Parent (JS oP)
open Spike.Lib.A64.Flow.Worker.Wake.MainPost (mainSp0)
open Spike.Lib.WakeSpawn (SpawnPrem)
open Spike.Lib.WakeMainHR (MainPieces)

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- **the segment-end fields of `MainPieces`** (see the module doc). -/
structure MainSeg (th : Thread isaLSE2) (c : Ctl) (Rm : Region) (F₂ : MachineData → Prop)
    (cA x29 ra tp : BitVec 64) : Prop where
  hhat : At (RuntimeLayout.ofPlaceW hp i).exe (endR hp i) ⟨Rm.base, -96, 16⟩ F₂
    ⟨cloneAt pfxM (RuntimeLayout.ofPlaceW hp i).exe, oP, JS c cA x29 ra tp⟩ th.st c
  hRb : (Rm.base.toNat : Int) = th.st.st.1.regs.SP.toNat + 80
  hRok : (⟨Rm.base, -96, 16⟩ : Region).OK
  hal : Rm.base.toNat % 16 = 0
  htp : tp = (RuntimeLayout.ofPlaceW hp i).pinA + 0#64 + 8#64
  hra : Int64.ofBitVec ra = (_root_.Executable.labels (RuntimeLayout.ofPlaceW hp i).exe).label mainSp0

/-- **`HMainR` from `MainSeg`, `hA` and `hZ`** (see the module doc). -/
theorem hMainR_ofD {asm : String} {E : Entry} {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {μ : Marks}
    {M : WakeM0.MSide (ιR hp i)} {r0 r1 : ιR hp i → Range}
    (hprog : o.prog = Spike.Lib.A64.WakeLabels.wakeProg)
    (hw : Scc.Cert.WideA64.ExeWide (RuntimeLayout.ofPlaceW hp i).exe)
    (hpv : ∀ d s, R1 d s → ∃ (Ent : Entry) (P : State → Prop), Ent.clear (RuntimeLayout.ofPlaceW hp i).Λ = true ∧
      Spike.Lib.DmemPriv.PrivInv abi P (RuntimeLayout.ofPlaceW hp i).Λ Ent d)
    (hpc : ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q,
      SpawnPrem (QG hp i arch R1 μ M r0 r1) (RuntimeLayout.ofPlaceW hp i).Λ asm E 0 d s th stack tls r →
      (wakeS arch).Run s [] s' →
      PreR hp i arch R1 μ M r0 r1 d th stack s s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q →
      ∃ c Rm F₂ cA x29 ra tp, MainSeg hp i th c Rm F₂ cA x29 ra tp ∧ lbl l = some cA.toNat ∧
        (RuntimeLayout.ofPlaceW hp i).stacksA.toNat + 4096 ≤ ((⟨Rm.base, -96, 16⟩ : Region).addr (-32)).toNat) :
    HMainR hp i asm E arch R1 μ M r0 r1 := by
  refine WakeMainHR.hMainR_of hp i hw hpv ?_
  intro d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q hP hrun hR
  obtain ⟨c, Rm, F₂, cA, x29, ra, tp, hM, hA, hZ⟩ :=
    hpc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hP hrun hR
  obtain ⟨htP, hlP, hwc, hval, hloc, hin⟩ := WakeMainSrcR.src_pieces_R hp i hR hR.hsp hA
  obtain ⟨Ent, P, hE, hc⟩ := hpv d s hP.1
  have hwf : (RuntimeLayout.ofPlaceW hp i).Λ.WF := PlaceW.wf_link_of_placeW i hp
  have hth0 : d.1.threads[0]? = some th := by rw [hR.pre.threads]; rfl
  obtain ⟨-, -, -, -, σ, hAbs, -, -⟩ := hM.hhat
  have h16 : Consumer1.LocIn (RuntimeLayout.ofPlaceW hp i).Λ.shared ⟨tp + 16#64, 8⟩ := by
    rw [hM.htp]; exact WakeMainInstD.locIn_tp16_I hp i
  have h8 : Consumer1.LocIn (RuntimeLayout.ofPlaceW hp i).Λ.shared ⟨tp + 8#64, 8⟩ := by
    rw [hM.htp]; exact WakeMainInstD.locIn_tp8_I hp i
  have hoff := fun {A} (hA : Consumer1.LocIn (RuntimeLayout.ofPlaceW hp i).Λ.shared ⟨A, 8⟩) =>
    WakeMainFlag.hAoff_of hc hE hwf hth0 hM.hRok (show (-96 : Int) % 8 = 0 by decide)
      (show (16 : Int) % 8 = 0 by decide) (show (-96 : Int) < 16 by decide) hAbs hA
  have hm : MemRelP (RuntimeLayout.ofPlaceW hp i).Λ w.1.lbl w.1.lsize ts d.1.mem s'.mem [] th.prom [] := by
    rw [hR.hw]; exact hR.pre.inv1.mem
  exact ⟨c, Rm, F₂, cA, x29, ra, tp, _, _,
    { hhat := hM.hhat, hRb := hM.hRb, hRok := hM.hRok, hal := hM.hal, htp := hM.htp, hra := hM.hra,
      htP := htP, hlP := hlP, hwc := hwc, hval := hval, hloc := hloc, hin := hin,
      hS := WakeMainInstD.hS_I hp i w.1 hm hM.htp (WakeMainFlag.hA0_of hc hE hwf hth0 h16 _ r) (hoff h16),
      htls := WakeMainInstD.htls_I hp i hprog hw w.2 hm hM.htp (WakeMainFlag.hA0_of hc hE hwf hth0 h8 _ r)
        (hoff h8) hZ hwc hval hloc hin,
      hexit := WakeMainInstD.hexit_I hp i w.1 }⟩

end Inst

end Spike.Lib.WakeMainHRD

/-- info: 'Spike.Lib.WakeMainHRD.hMainR_ofD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeMainHRD.hMainR_ofD
