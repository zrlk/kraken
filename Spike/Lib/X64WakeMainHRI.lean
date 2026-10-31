/-
**wake.w on x86-64: `HMainR` from the segment end alone** (in the manner of
`Spike/Lib/WakeMainHRD.lean`'s `hMainR_ofD`): `hMainR_I`,
`X64WakeMainHR.hMainR_of` with every `MainPieces` field supplied inside
except the frame pointer `hfp` and the park's code facts `hpcode`/`hpentry`.

At `cP = Ctl.of s0`, `c`'s word `cst (.loc ⟨l,0⟩ 0)` at `.ptr .pub .int`:

- `seg` and the frame's guard bound by `X64.Flow.WakeWc.mainSeg_of` at main's
  `ClonePost` (`hpost`) and `PreR`'s `clone`, `hc`, `pre.threads`;
- `htP`, `hlP`, `hwc`, `hval`, `hloc`, `hin` by
  `X64WakeMainSrcR.src_pieces` (`PreR.hsp`, `hc`, `hin`, `hw`, the label's
  placement from `mainSeg_of`);
- `hS` by `X64WakeMainInstD.hS_I` lifted to `wakeMs` (`permit_notIn`) and
  to `msM` (`X64WakeInst.stOk_msM_park`, the TCB room and `tcb2`'s word off
  the park's, `X64WakeSelfOK`);
- `hlim` by `limOk_I` (`cT_ne_I` at `GhOK`, `Z` the guard bound at offset
  `-16`) lifted by `limOk_msM`; `hT`: the TCB word `tcbM L` is in `pinned`
  (shared, mapped), outside every label (`SelfOK`) and unloadable in main's
  frame; the three `hA0`/`hoff` by `X64WakeMainFlag.hA0_of`/`hAoff_of` at
  `R1`'s private-memory invariant (`hpv`) and `hat`'s `Abs`;
- `hexit` by `hexit_I`; `hmA` by `X64WakeLabMapped.mapped_K0_of_shared` at
  `X64WakeMainHR.locIn_cA`; `hmP`, `hmE` by `labMapped_of_noPtr` (the tail
  call `mTail`, the test `wlIf`: no label access).

**Premises**: `hw`, `hpv` (as `hMainR_of`); `hpost` (main's `ClonePost` at
the clone, the wc segment's exit: X64-endR); `hfp` (main's frame pointer at
the clone's `MainSeg` is `RW Rm`'s word `48`); `hpcode`, `hpentry` (the
park's code facts at the layout's executable).

**Unlike AArch64** (forced by the x64 shape):
- `hS`, `hlim`, `hT` are stated at `msM` (main owns its TCB word, its runtime
  writes off both self words), so the `msOf` lemmas of `X64WakeMainInstD` are
  lifted through `wakeMs` (`¬ InLabel` for stores) to `msM`.
- `hT` (main's `%fs:0` load) and the mapped rows `hmA`/`hmP`/`hmE` are
  discharged here (A64 has none of them).
- There is no `htls`: the wait loop takes the limit's `LimOk` (`hlim`).
- `hpost` fixes the clone's control to `Ctl.of s0`, as the x64 `MainWS` has
  one control `cP`.
-/
import Spike.Lib.X64WakeMainHR
import Spike.Lib.X64WakeMainInstD
import Spike.Lib.X64WakeMainSrcR
import Spike.Lib.X64WakeInstMsM
import Spike.Lib.X64WakeLabMapped

namespace Spike.Lib.X64WakeMainHRI

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64WakeA64 Spike.Lib.Handover Spike.Lib.X64WakeSpawnR
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.Rt.PreChild (r1Of)
open Spike.Lib.X64WakeInst (Gh wakeMs msM)
open Spike.Lib.X64.WakePh (tcbM tcb2)
open Spike.Lib.X64.Flow.Ret0 (LimOk StOk LdOk)
open Spike.Lib.X64WakeSpawn (SpawnPrem)
open Spike.Lib.X64WakeMainHR (MainPieces RW m0)

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

/-- **main's TCB word is shared** (`pinned`). -/
theorem locIn_tp_I : Consumer1.LocIn (Ly).Λ.shared ⟨tcbM (Ly), 8⟩ := by
  intro k hk
  exact .inr (.inr (X64WakeMainInstD.pinned_j hp i (j := 1) (by decide) (by decide) k
    (by simpa [Scc.Sem.Kernel.locBytes] using hk)))

/-- **`HMainR` from main's `ClonePost`, `hfp` and the park's code facts**
(see the module doc). -/
theorem hMainR_I {asm : Asm} {E : Entry} {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {μ : Marks}
    {M : X64WakeM0.MSide (ιR hp i)} {r0 r1 : ιR hp i → Range}
    (hw : Scc.Cert.WideX64.ExeWide (Ly).exe)
    (hpv : ∀ d s, R1 d s → ∃ (Ent : Entry) (P : State → Prop), Ent.clear (Ly).Λ = true ∧
      Spike.Lib.DmemPriv.PrivInv abi P (Ly).Λ Ent d)
    (hpost : ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q,
      SpawnPrem (QG hp i arch R1 μ M r0 r1) (Ly).Λ asm E 0 d s th stack tls r →
      (wakeS arch).Run s [] s' →
      PreR hp i arch R1 μ M r0 r1 d th stack s s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q →
      ∃ J t, Spike.Lib.X64.Flow.WakeWc.ClonePost (Ly) (X64WakeAssemblyR.endR hp i) J t th.st (Ctl.of s0))
    (hfp : ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q,
      SpawnPrem (QG hp i arch R1 μ M r0 r1) (Ly).Λ asm E 0 d s th stack tls r →
      (wakeS arch).Run s [] s' →
      PreR hp i arch R1 μ M r0 r1 d th stack s s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q →
      ∀ Rm F₂ cA fp ra tp,
        X64WakeMainHRD.MainSeg (Ly) (X64WakeAssemblyR.endR hp i) th (Ctl.of s0) Rm F₂ cA fp ra tp →
        fp = (RW Rm).addr 48)
    (hpcode : ∃ (c0' : Ctl) (rbp0' ra' tp' : BitVec 64),
      Park.Code c0' rbp0' ra' tp' (Ly).exe (X64WakeAssemblyR.endR hp i))
    (hpentry : (_root_.Executable.labels (Ly).exe).label ".Lscc_rt_park.entry" =
      (_root_.Executable.labels (Ly).exe).label "scc_rt_park" + 8) :
    HMainR hp i asm E arch R1 μ M r0 r1 := by
  refine X64WakeMainHR.hMainR_of hp i hw hpv ?_
  intro d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q hP hrun hR
  obtain ⟨J, t, hpo⟩ := hpost _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hP hrun hR
  obtain ⟨th0, hs, hc⟩ := hR.hc
  obtain ⟨Rm, F₂, cA, fp, ra, tp, hM, hA, hZ⟩ :=
    Spike.Lib.X64.Flow.WakeWc.mainSeg_of hpo hR.clone hs hc hR.pre.threads
  have hfp' := hfp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hP hrun hR _ _ _ _ _ _ hM
  -- the record's fields
  have elbl : w.val.lbl = lbl := by rw [hR.hw]; rfl
  have elsz : w.val.lsize = lsize := by rw [hR.hw]; rfl
  have ecS : w.val.cS = ⟨l, 0⟩ := by rw [hR.hw]; rfl
  have hA' : w.val.lbl l = some cA.toNat := by rw [elbl]; exact hA
  -- the source fields
  obtain ⟨th0', ws, hs', hsp⟩ := hR.hsp
  obtain rfl : th0' = th0 := by
    rw [hs] at hs'; exact (List.singleton_inj.mp (congrArg Array.toList hs')).symm
  obtain ⟨htP, hlP, hwc, hval, hloc, hin⟩ := X64WakeMainSrcR.src_pieces (lsize := w.val.lsize) hsp hs
    hR.pre.ths hc hA' (by rw [elsz]; exact hR.hin) ecS
  -- the frame facts
  have hg := w.2.1
  have hself := w.2.2
  obtain ⟨Ent, P, hE, hpi⟩ := hpv d s hP.1
  have hwf := X64WakeQ.hwf_ofPlaceOK hp i
  have hth0 : d.1.threads[0]? = some th := by rw [hR.pre.threads]; rfl
  have hat := hM.hat hR.clone hR.pre.threads
  obtain ⟨-, -, -, -, σ, hAbs, -, -⟩ := hat
  have hoff := fun {A} (hA : Consumer1.LocIn (Ly).Λ.shared ⟨A, 8⟩) =>
    X64WakeMainFlag.hAoff_of hpi hE hwf hth0 hM.wideOK (show (-80 : Int) % 8 = 0 by decide)
      (show (40 : Int) % 8 = 0 by decide) (show (-80 : Int) < 40 by decide) hAbs hA
  have hA0 := fun {A} (hA : Consumer1.LocIn (Ly).Λ.shared ⟨A, 8⟩) =>
    X64WakeMainFlag.hA0_of hpi hE hwf hth0 hA ((r1Of (Ly).lab).lo + (r1Of (Ly).lab).size) r
  have hm : MemRelP (Ly).Λ w.val.lbl w.val.lsize ts d.1.mem s'.mem [] th.prom [] := by
    rw [hR.hw]; exact hR.pre.inv1.mem
  have htpT : tp = tcbM (Ly) := by rw [hM.htp, BitVec.add_zero]
  have h16 : Consumer1.LocIn (Ly).Λ.shared ⟨tp + 16#64, 8⟩ := by
    rw [hM.htp]; exact X64WakeMainInstD.locIn_tp16_I hp i
  have h8 : Consumer1.LocIn (Ly).Λ.shared ⟨tp + 8#64, 8⟩ := by
    rw [hM.htp]; exact X64WakeMainInstD.locIn_tp8_I hp i
  have h0 : Consumer1.LocIn (Ly).Λ.shared ⟨tp, 8⟩ := by rw [htpT]; exact locIn_tp_I hp i
  have hroom := Spike.Lib.X64WakeInst.pin_room_ofPlaceWX hp i
  -- `hS`
  have hS0 := X64WakeMainInstD.hS_I hp i hm (rd := fun w => ∃ n, w.val = .num n) (own := fun _ => [])
    (cT := w.val.cT) hM.htp (R := RW Rm) (hA0 h16) (hoff h16)
  have hSw : StOk (wakeMs hp i w.val) (DFrame (RW Rm) (m0 hp i d th r)) (tp + 16#64) 0#64 :=
    ⟨hS0.rt, ⟨hS0.mp.1, fun _ => ⟨hS0.mp.2 rfl, by rw [hM.htp]; exact X64WakeMainInstD.permit_notIn hp i hm⟩⟩,
      hS0.G, hS0.unmapped⟩
  rw [htpT] at hSw
  have hS := Spike.Lib.X64WakeInst.stOk_msM_park hp i (T := tcbM (Ly)) (W := tcb2 (Ly)) hSw
    (Spike.Lib.X64WakeInst.tcbM_room _ hroom) (Spike.Lib.X64WakeInst.offTcb_park_tcb2 _ hroom)
  -- `hlim`
  obtain ⟨-, -, -, ⟨b, hl, ho, hT⟩, -⟩ := hg
  have hZ' : (Ly).stacksA.toNat + 4096 ≤ (((RW Rm).fp 8).addr 0 - 8#64 - (16 : Int64).toBitVec).toNat := by
    have e : ((RW Rm).fp 8).addr 0 - 8#64 - (16 : Int64).toBitVec = (⟨Rm.base, -64, 16⟩ : Region).addr (-16) := by
      rw [Region.fp_addr]; simp only [Region.addr]
      have e1 : BitVec.ofInt 64 (8 + 0) = 8#64 := by decide
      have e2 : BitVec.ofInt 64 (-16) = 0#64 - 16#64 := by decide
      have e3 : (16 : Int64).toBitVec = 16#64 := by decide
      rw [e1, e2, e3]; bv_omega
    rw [e]; exact hZ (-16) (by decide) (by decide)
  have hL0 := X64WakeMainInstD.limOk_I hp i hm (rd := fun w => ∃ n, w.val = .num n) (own := fun _ => [])
    (X64WakeMainInstD.cT_ne_I hp i hm hl ho hT) hM.htp (R := RW Rm) (hA0 h8) (hoff h8) hZ'
  have e8 : tp + (8 : Int64).toBitVec = tp + 8#64 := by
    have : (8 : Int64).toBitVec = 8#64 := by decide
    rw [this]
  have hLw : LimOk (wakeMs hp i w.val) (DFrame (RW Rm) (m0 hp i d th r)) (tp + (8 : Int64).toBitVec)
      (((RW Rm).fp 8).addr 0 - 8#64 - (16 : Int64).toBitVec) := by
    rw [e8]; exact ⟨hL0.rt, ⟨hL0.mp.1, nofun⟩, hL0.unmapped, hL0.room⟩
  -- `hT`
  have hTw : LdOk (wakeMs hp i w.val) (DFrame (RW Rm) (m0 hp i d th r)) tp := by
    refine ⟨?_, ⟨X64WakeLabMapped.mapped_K0_of_shared h0 false, nofun⟩,
      X64WakeMainInstD.unmapped_I (hA0 h0) (hoff h0)⟩
    rw [htpT]; exact hself.2.1
  refine ⟨Rm, F₂, cA, fp, ra, tp, TermRun.cst (.loc ⟨l, 0⟩ 0), .ptr .pub .int, ?_⟩
  exact {
    seg := hM
    hfp := hfp'
    htP := htP
    hlP := hlP
    hwc := hwc
    hval := hval
    hloc := hloc
    hin := hin
    hlim := Spike.Lib.X64WakeInst.limOk_msM hp i hLw
    hT := Spike.Lib.X64WakeInst.ldOk_msM hp i hTw
    hS := by rw [htpT]; exact hS
    hpcode := hpcode
    hpentry := hpentry
    hexit := X64WakeMainInstD.hexit_I (fun _ h => h) (fun _ _ h => h)
    hmA := X64WakeLabMapped.mapped_K0_of_shared (X64WakeMainHR.locIn_cA w.2.1 (hwc ▸ hval))
    hmP := X64WakeLabMapped.labMapped_of_noPtr (X64WakeLabMapped.noPtr_of_term fun x op e h => by
      rw [htP] at h; cases h)
    hmE := fun c ⟨_, _, hc⟩ => X64WakeLabMapped.labMapped_of_noPtr (X64WakeLabMapped.noPtr_of_term
      fun x op e h => by rw [hc] at h; cases h) }

end Inst

/-- info: 'Spike.Lib.X64WakeMainHRI.locIn_tp_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms locIn_tp_I

/-- info: 'Spike.Lib.X64WakeMainHRI.hMainR_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hMainR_I

end Spike.Lib.X64WakeMainHRI
