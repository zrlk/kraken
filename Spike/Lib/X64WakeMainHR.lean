/-
**wake.w on x86-64: `HMainR`, assembled** (in the manner of
`Spike/Lib/WakeMainHR.lean`): `hMainR_of`, `X64WakeSpawnR.HMainR` from the
pieces per witness tuple (`MainPieces`), at main's post-spawn region
`R = ⟨Rm.base, -80, 40⟩` and the frame condition `F = DFrame R m0` of main's
memory `m0` after the clone.

Closed here (the glue `X64WakeSpawnR.MainWS` needs beyond the pieces):

- `hat` by `X64WakeMainHRD.MainSeg.hat` (the clone's `At` widened to `R`,
  from `PreR.clone`), `hRb` from `MainSeg.hRb`, `hRlo`/`hRhi` by `rfl`, `hR`
  by `MainSeg.wideOK`;
- `htop`: the handed range `r1Of L.lab` is owned (`ClonePre`), so in the pool,
  which fits the address space (`pool_fit`);
- `hFR` by definition, `hF` by `FStable.dframe`;
- `hdm`: the flag's word `cA` (shared by `GhOK`, `locIn_cA`) does not load
  from `m0` (`X64WakeMainFlag.hA0_of`) and is off `R` (`hAoff_of` at `hat`'s
  `Abs`), at `R1`'s private-memory invariant (`hpv`);
- `hown` by `X64WakeOwnX.ownAt_msXW` (`tp = tcbM L`), `htp4` from `htp` and
  `X64WakeChildSt.childSt_al`, `hwide` by `WorkerSide.wideX_of` (`hw`).

`MainPieces` is what remains, at main's thread `th` after the clone, the
record `g` and `cP = Ctl.of s0`:

- the segment end (`X64WakeSpawnR.hpc_of`): `seg` (`MainSeg`) and `hfp`;
- the source side (`X64WakeMainSrcR.src_pieces`): `htP`, `hlP`, `hwc`,
  `hval`, `hloc`, `hin`;
- the instance (`X64WakeMainInstD`, the code facts, the mapped rows): `hlim`,
  `hT`, `hS`, `hpcode`, `hpentry`, `hexit`, `hmA`, `hmP`, `hmE` at
  `msM g` and `F`.

**Unlike AArch64** (forced by the x64 shape):
- The pieces fill the x64 `MainWS` (`main_closed_ws`'s hypotheses) directly:
  one region `R` and frame `F` (no frame family `γ`, so no
  `WakeMainFrames.frames_unit`), no `htls`/`hal`.
- The clone's `At` is on `wc_main`'s frame `[-64, 16)` and is widened to
  `R = [-80, 40)` (`MainSeg.hat`); A64's region is the same before and after.
- main owns its TCB word (`hown`, `htp4`), and the mapped rows
  (`hmA`, `hmP`, `hmE`) are pieces.
-/
import Spike.Lib.X64WakeSpawnR
import Spike.Lib.X64WakeMainFlag

namespace Spike.Lib.X64WakeMainHR

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64WakeA64 Spike.Lib.Handover Spike.Lib.X64WakeSpawnR
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.Rt.PreChild (r1Of)
open Spike.Lib.X64WakeInst (Gh msM)
open Spike.Lib.X64WakeInstFields (GhOK)
open Spike.Lib.X64WakePreA (cloneAt)
open Spike.Lib.X64.WakePh (tcbM tcb2)
open Spike.Lib.X64.WakePh.MainPost (mainX2)
open Spike.Lib.X64.WaitLoop (RdOne Past)
open Spike.Lib.X64.Flow.Ret0 (LimOk StOk LdOk)
open Spike.Lib.X64WakeMainSrc (waitC)
open Spike.Lib.X64WakeM0 (mTail wlIf)
open Spike.Lib.X64WakeSpawn (SpawnPrem)

/-- **The flag's word is shared**: `cA` the address `GhOK`'s `cS`
represents. -/
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

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

/-- main's memory after the clone. -/
abbrev m0 (d : Cfg) (th : Thread isa) (r : BitVec 64) : MachineData :=
  (Kernel.retThread abi (parentPre abi d.2 0 th ((r1Of (Ly).lab).lo + (r1Of (Ly).lab).size)) r).st.st.1

/-- main's post-spawn region. -/
abbrev RW (Rm : Region) : Region := ⟨Rm.base, -80, 40⟩

/-- **The pieces of `MainWS`** at one witness tuple (see the module
doc); the frame condition is `DFrame (RW Rm) (m0 d th r)`. -/
structure MainPieces (g : Gh) (d : Cfg) (th : Thread isa) (r : BitVec 64) (cP : Ctl) (Rm : Region)
    (F₂ : MachineData → Prop) (cA fp ra tp : BitVec 64) (w : TermRun.Word) (tyP : Ty) : Prop where
  /- the segment end -/
  seg : X64WakeMainHRD.MainSeg (Ly) (X64WakeAssemblyR.endR hp i) th cP Rm F₂ cA fp ra tp
  hfp : fp = (RW Rm).addr 48
  /- the source side -/
  htP : cP.term = mTail
  hlP : TermRun.lookupE cP.env "c" = some (tyP, [w])
  hwc : w.val = .loc g.cS 0
  hval : ValRep g.lbl w.val cA.toNat
  hloc : LocRep g.lbl w.val cA.toNat 0
  hin : ∃ sa, w.val = .loc sa 0 ∧ sa.offset < g.lsize sa.label
  /- the instance -/
  hlim : LimOk (msM hp i (tcbM (Ly)) (tcb2 (Ly)) g) (DFrame (RW Rm) (m0 hp i d th r))
    (tp + (8 : Int64).toBitVec) (((RW Rm).fp 8).addr 0 - 8#64 - (16 : Int64).toBitVec)
  hT : LdOk (msM hp i (tcbM (Ly)) (tcb2 (Ly)) g) (DFrame (RW Rm) (m0 hp i d th r)) tp
  hS : StOk (msM hp i (tcbM (Ly)) (tcb2 (Ly)) g) (DFrame (RW Rm) (m0 hp i d th r)) (tp + 16#64) 0#64
  hpcode : ∃ (c0' : Ctl) (rbp0' ra' tp' : BitVec 64),
    Park.Code c0' rbp0' ra' tp' (Ly).exe (X64WakeAssemblyR.endR hp i)
  hpentry : (_root_.Executable.labels (Ly).exe).label ".Lscc_rt_park.entry" =
    (_root_.Executable.labels (Ly).exe).label "scc_rt_park" + 8
  hexit : ∀ s c, Past (waitC w) "d" wlIf (.ptr .pub .int) (RdOne (ms := msM hp i (tcbM (Ly)) (tcb2 (Ly)) g) g.lbl) c →
    At (Ly).exe (X64WakeAssemblyR.endR hp i) ((RW Rm).fp 8) (DFrame (RW Rm) (m0 hp i d th r))
      ⟨(_root_.Executable.labels (Ly).exe).label mainX2 + 4 + 4 + 5, ⟨8, [(.rbp, 40)]⟩,
        fun σ _ => σ.regs.rdi.toBitVec = 0#64⟩ s c → ¬ (msM hp i (tcbM (Ly)) (tcb2 (Ly)) g).abortAt s →
    MainExit Spike.Lib.X64WakeT1.wakeSrc (msM hp i (tcbM (Ly)) (tcb2 (Ly)) g) s c 0
  hmA : ∀ wr, Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 (Ly).Λ) wr ⟨cA, 8⟩ = true
  hmP : Spike.Lib.X64WakeMappedRow.LabMapped g.lbl (Spike.Lib.X64Consumer.K0 (Ly).Λ) cP
  hmE : ∀ c, Past (waitC w) "d" wlIf (.ptr .pub .int) (RdOne (ms := msM hp i (tcbM (Ly)) (tcb2 (Ly)) g) g.lbl) c →
    Spike.Lib.X64WakeMappedRow.LabMapped g.lbl (Spike.Lib.X64Consumer.K0 (Ly).Λ) c

/-- **`HMainR` from the pieces** (see the module doc). -/
theorem hMainR_of {asm : Asm} {E : Entry} {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {μ : Marks}
    {M : X64WakeM0.MSide (ιR hp i)} {r0 r1 : ιR hp i → Range}
    (hw : Scc.Cert.WideX64.ExeWide (Ly).exe)
    (hpv : ∀ d s, R1 d s → ∃ (Ent : Entry) (P : State → Prop), Ent.clear (Ly).Λ = true ∧
      Spike.Lib.DmemPriv.PrivInv abi P (Ly).Λ Ent d)
    (hpc : ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q,
      SpawnPrem (QG hp i arch R1 μ M r0 r1) (Ly).Λ asm E 0 d s th stack tls r →
      (wakeS arch).Run s [] s' →
      PreR hp i arch R1 μ M r0 r1 d th stack s s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q →
      ∃ Rm F₂ cA fp ra tp cw tyP, MainPieces hp i w.1 d th r (Ctl.of s0) Rm F₂ cA fp ra tp cw tyP) :
    HMainR hp i asm E arch R1 μ M r0 r1 := by
  intro d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q hP hrun hR
  obtain ⟨Rm, F₂, cA, fp, ra, tp, cw, tyP, hM⟩ := hpc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hP hrun hR
  have hg := w.2.1
  have hth := hR.pre.threads
  have hth0 : d.1.threads[0]? = some th := by rw [hth]; rfl
  have hone : ∀ th' : Thread isa, d.1.threads = #[th'] → th' = th := fun th' h' => by
    rw [hth] at h'; exact (List.singleton_inj.mp (congrArg Array.toList h')).symm
  obtain ⟨_thc, _, _, _, _, _, -, -, -, -, -, -, -, -, -, -, -, -, -, hO1, -⟩ := hR.clone
  obtain ⟨Ent, P, hE, hc⟩ := hpv d s hP.1
  have hwf := X64WakeQ.hwf_ofPlaceOK hp i
  have hA := locIn_cA hg (hM.hwc ▸ hM.hval)
  have hat := hM.seg.hat hR.clone hth
  have hok := hM.seg.wideOK
  have hat' := hat
  obtain ⟨-, -, -, -, σ, hAbs, -, -⟩ := hat'
  have hoff := X64WakeMainFlag.hAoff_of hc hE hwf hth0 hok (show (-80 : Int) % 8 = 0 by decide)
    (show (40 : Int) % 8 = 0 by decide) (show (-80 : Int) < 40 by decide) hAbs hA
  have hA0 := X64WakeMainFlag.hA0_of hc hE hwf hth0 hA ((r1Of (Ly).lab).lo + (r1Of (Ly).lab).size) r
  have htop : (r1Of (Ly).lab).lo + (r1Of (Ly).lab).size ≤ 2 ^ 64 := by
    have h1 := hO1.1
    have h2 := (Ly).pool_fit
    simp only [Range.Sub] at h1
    omega
  have htpT : tp = tcbM (Ly) := by rw [hM.seg.htp, BitVec.add_zero]
  have htp4 : (tp + 16#64).toNat % 4 = 0 := by
    have e : tp + 16#64 = (Ly).pinA + 24#64 := by rw [htpT]; bv_omega
    rw [e]; exact X64WakeChildSt.childSt_al hp i
  have elbl : w.val.lbl = lbl := by rw [hR.hw]; rfl
  have elsz : w.val.lsize = lsize := by rw [hR.hw]; rfl
  rw [← elbl, ← elsz]
  refine ⟨Ctl.of s0, RW Rm, F₂, DFrame (RW Rm) (m0 hp i d th r), cA, fp, ra, tp, cw, tyP, rfl, ?_⟩
  exact {
    hat := fun th' h' => by rw [hone th' h']; exact hat
    hRb := fun th' h' => by rw [hone th' h']; exact hM.seg.hRb
    hRlo := rfl
    hRhi := rfl
    hR := hok
    htop := htop
    htP := hM.htP
    hlP := hM.hlP
    hval := hM.hval
    hloc := hM.hloc
    hin := hM.hin
    hFR := fun th' h' m hm => by rw [hone th' h'] at hm; exact hm
    hF := FStable.dframe _ _
    hlim := hM.hlim
    hdm := fun m hm => (hm cA hoff.1 hoff.2).trans hA0
    hT := hM.hT
    hown := by rw [htpT]; exact X64WakeOwnX.ownAt_msXW
    hS := hM.hS
    htp4 := htp4
    hpcode := hM.hpcode
    hpentry := hM.hpentry
    hfp := hM.hfp
    hra := hM.seg.hra
    hexit := hM.hexit
    hwide := fun s he hd => X64WakeW1.WorkerSide.wideX_of hw he hd
    hmA := hM.hmA
    hmP := hM.hmP
    hmE := hM.hmE }

end Inst

/-- info: 'Spike.Lib.X64WakeMainHR.locIn_cA' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms locIn_cA

/-- info: 'Spike.Lib.X64WakeMainHR.hMainR_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hMainR_of

end Spike.Lib.X64WakeMainHR
