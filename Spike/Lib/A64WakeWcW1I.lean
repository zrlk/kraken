/-
**`wc_main`'s own nodes inside `h1`'s level `W1W`** (AArch64; `H1G.wcWf`).

- `wcMainW_W1`: `WcMainW` at `W1W … l b n` (no frames, no outside moves)
  from its ten fields.
- `wcMidW_st`: every node's `SFactsSt2` at `ownG` (`WcMidWG.wcMidW_wcG` at
  `ofPlaceW` and the loader's facts).
- `bl_W1`, `blkG`/`blks_W1`, `nodeG`/`nodes_W1`: each field inside `W1W`,
  from `wcMidW_st` and `PlacedLy.wcMainW_placed` (`WcWf.blkW_wfC`,
  `WcWf.nodeW_wfC`, `CalWf.nodeCst`).
- `wcMainW_wf`: `H1G.wcWf` from the loader's facts, `BoxPure`, and the
  per-node word premises of `wcMidW_wcG`.

The proofs decide pcs at the certificate's labels; no absolute address
appears in a statement.
-/
import Spike.Lib.A64WakeH1Root
import Spike.Lib.A64WakeWcMidW
import Spike.Lib.A64WakePlacedLy
import Spike.Lib.A64WakeWfCalW1
import Spike.Lib.A64WakeWfCalOff
import Spike.Lib.Hello1Runs

namespace Spike.Lib.WakeWcW1I

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.WakeWc
open Spike.Lib.A64.WakePh.WcSp4 (wcNI sp4A initCall sp6A cloneArgs)
open Spike.Lib.A64.WakePh.Tcb2Call (wcN3 tcb2Call)
open Spike.Lib.A64.KeepTP (tpXa)
open Spike.Lib.WakeOPremW (W1W)
open Spike.Lib.WakeHMid (SB QB BoxPure)
open Spike.Lib.A64.Rt.Reserve (ntA)
open Spike.Lib.A64ConsumerA (SFactsSt2)
open Spike.Lib.A64.WakePh (ownG)
open Spike.Lib.A64.WakeLabels (wakeProg)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Scc.Sem.Entry) (cT : Loc) (Dt : State → Prop) (Ctx : FragS isaLSE2)
  (ls0 : Spike.Lib.A64Consumer.Lsize)

set_option hygiene false in
/-- The layout of `ofPlaceW`. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hp i

set_option hygiene false in
/-- `h1`'s memory side at no frames. -/
local notation "ms1" => WakeH1Inv.ms1W hp i E cT ls0 l b n []

set_option hygiene false in
/-- `h1`'s level at no frames. -/
local notation "Wq" => fun s c => W1W hp i E Dt Ctx ls0 l b n s c []

set_option hygiene false in
/-- The layout's labels. -/
local notation "LB" => (_root_.Executable.labels (Ly).exe).label

set_option hygiene false in
/-- The ghost premise of `WcMainW`'s per-ghost fields. -/
local notation "MG" => MidG (SB l b) c0 cA ∧ FrG J0 fr ∧ FrMG J0 fr m

/-- **`wc_main`'s own nodes inside `W1W`** (`H1G.wcWf`), from its fields;
each `h<field>` is the field of `WcMainW` of the same name, not yet
discharged here. -/
theorem wcMainW_W1 {l : WeakMem.AllocLabel} {b n : Nat} {R : Region} {F : MachineData → Prop}
    {J0 : AS → Ctl → Prop} {t : UInt64}
    (hf : NodeW Wq (fun _ _ => False) (Ly).exe (WakeSpawnR.endR hp i) R F (rNQ (tpXa ms1 t) LB J0 (SB l b) (QB l b) .f))
    (hbl : BlkW Wq (fun _ _ => False) (Ly).exe (WakeSpawnR.endR hp i) R F (rN (tpXa ms1 t) LB J0 (SB l b) .bl) resB)
    (hsp3 : ∀ c0 cA m fr, MG →
      BlkW Wq (fun _ _ => False) (Ly).exe (WakeSpawnR.endR hp i) R F (wcN3 LB (j3 cA m fr) c0) tcb2Call)
    (hn4 : ∀ c0 cA m fr, MG →
      BlkW Wq (fun _ _ => False) (Ly).exe (WakeSpawnR.endR hp i) R F (aN LB c0 (t2 LB) cA m fr .n4) sp4A)
    (hn4s : ∀ c0 cA m fr, MG →
      NodeW Wq (fun _ _ => False) (Ly).exe (WakeSpawnR.endR hp i) R F (aN LB c0 (t2 LB) cA m fr .n4s))
    (hn5 : ∀ c0 cA m fr, MG →
      BlkW Wq (fun _ _ => False) (Ly).exe (WakeSpawnR.endR hp i) R F (aN LB c0 (t2 LB) cA m fr .n5) initCall)
    (hnI : ∀ c0 cA m fr, MG →
      NodeW Wq (fun _ _ => False) (Ly).exe (WakeSpawnR.endR hp i) R F (wcNI LB c0 (t2 LB) cA m fr))
    (hn6 : ∀ c0 cA m fr, MG →
      BlkW Wq (fun _ _ => False) (Ly).exe (WakeSpawnR.endR hp i) R F (bN LB c0 (t2 LB) cA m fr .n6) sp6A)
    (hn6f : ∀ c0 cA m fr, MG →
      NodeW Wq (fun _ _ => False) (Ly).exe (WakeSpawnR.endR hp i) R F (bN LB c0 (t2 LB) cA m fr .n6f))
    (hn6a : ∀ c0 cA m fr, MG →
      BlkW Wq (fun _ _ => False) (Ly).exe (WakeSpawnR.endR hp i) R F (bN LB c0 (t2 LB) cA m fr .n6a) cloneArgs) :
    WcMainW Wq (fun _ _ => False) (Ly).exe (WakeSpawnR.endR hp i) R F F (tpXa ms1 t) J0 (SB l b) (QB l b) :=
  ⟨hf, hbl, hsp3, hn4, hn4s, hn5, hnI, hn6, hn6f, hn6a⟩

/-- **`wc_main`'s nodes inside `SFactsSt2` at `ownG`** at `ofPlaceW`'s
layout and one ghost of `Box` (`WcMidWG.wcMidW_wcG` at the loader's facts):
the per-node `hst` of `wcMainW_W1`'s fields. The words' premises are those
of `wcMidW_wcG`; `hunN`, `hunP`, `hunH` are `H1G`'s fields. -/
theorem wcMidW_st (hpa : Scc.Sem.A64.textProgram SccCertificate.asm = .ok o.prog)
    (hwp : Scc.Sem.A64.textProgram SccCertificate.asm = .ok wakeProg)
    (hlo0 : Λ0.code.lo = Spike.Lib.A64.WakePh.lo)
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    {l : WeakMem.AllocLabel} {b n : Nat} {F0 : MachineData → Prop} {R : Region} {F : MachineData → Prop}
    {J0 : AS → Ctl → Prop} {t : UInt64} (hB : BoxPure (Ly) F0 n R F J0 t)
    (hunN : ∀ m, F m → Mem.loadInt m.dmem (ntA (Ly).lab) 8 = none)
    (hb : Spike.Lib.A64.WakePh.Tcb2CallW.BandSp3 (Ly) R)
    (hhdr : (Ly).pinA + 80#64 + 16#64 ∉ [(Ly).pnA, (Ly).lockA, (Ly).freeNA, (Ly).nextA, ntA (Ly).lab])
    (hmP : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 (Ly).Λ) true ⟨(Ly).pnA, 8⟩ = true)
    (hmH : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 (Ly).Λ) true ⟨(Ly).pinA + 96#64, 8⟩ = true)
    (hunP : ∀ m, F m → Mem.loadInt m.dmem (Ly).pnA 8 = none)
    (hunH : ∀ m, F m → Mem.loadInt m.dmem ((Ly).pinA + 96#64) 8 = none)
    (hband : Spike.Lib.A64.WakePh.WcSp4W.BandTi (Ly) R)
    (htidW : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 (Ly).Λ) true ⟨t2 (Ly).lab + 56#64, 8⟩ = true ∧
      (∀ m', F m' → Mem.loadInt m'.dmem (t2 (Ly).lab + 56#64) 8 = none) ∧
      ∀ w, (⟨t2 (Ly).lab + 56#64, 8⟩, w) ∉ Spike.Lib.A64.WakePh.own2a (Ly) (ntA (Ly).lab) 0) :
    WcMidW (fun s _ => SFactsSt2 (Ly).Λ (Spike.Lib.A64.PhRec.μ (Ly)) (ownG (Ly) (ntA (Ly).lab)) s)
      (Spike.Lib.A64.PhRec.K (Ly) ⟨0, 0⟩) (Ly).exe (Ly).endPc R F F (tpXa ms1 t) J0 (SB l b) (QB l b) := by
  have hpg := WakeSrcCtl.oprog_W hpa hwp
  have hlo := Spike.Lib.A64.WakePh.StartPlaceLy.hlo_W hp i hlo0
  have hs := Spike.Lib.A64.WakePh.StartPlaceLy.wsep_W hp i hA13
  obtain ⟨⟨hR, hal, -, hRlo, hhi, -, -⟩, -⟩ := hB
  exact Spike.Lib.A64.WakePh.WcMidWG.wcMidW_wcG (L := Ly) hpg hlo
    (Spike.Lib.PlaceW.abortLbl_of_placeW (Spike.Lib.PlaceW.link i hp))
    (fun l x h => Spike.Lib.PlaceW.hlab_ofPlaceW hp i l x (by rw [hlo, hpg]; exact h))
    (Spike.Lib.PlaceW.site_ofPlaceW hp i) hR hal hRlo hhi ⟨0, 0⟩
    (Spike.Lib.A64.WakePh.CalWf.sepN_W hp i hA13) (Spike.Lib.A64.WakePh.CalWf.hmN_W hp i hA13 true) hunN hb
    ⟨hs.pn_lock, hs.pn_freeN, hs.pn_next, hs.pn_a⟩ hhdr hmP hmH hunP hunH hband htidW

set_option hygiene false in
/-- `wc_main`'s nodes inside `SFactsSt2` at `ownG` (`wcMidW_st`'s). -/
local notation "STW" => WcMidW (fun s _ => SFactsSt2 (Ly).Λ (Spike.Lib.A64.PhRec.μ (Ly)) (ownG (Ly) (ntA (Ly).lab)) s)
  (Spike.Lib.A64.PhRec.K (Ly) ⟨0, 0⟩) (Ly).exe (Ly).endPc R F F (tpXa ms1 t) J0 (SB l b) (QB l b)

set_option hygiene false in
/-- `wc_main`'s nodes placed (`PlacedLy.wcMainW_placed`'s). -/
local notation "PLW" => WcMainW (fun s c => Spike.Lib.A64ConsumerS.PlacedSE (Ly).Λ
  (Spike.Lib.A64.WakePh.PlacedLy.lblL (Ly).Λ l b) s c []) (fun _ _ => False) (Ly).exe (Ly).endPc R F F
  (tpXa ms1 t) J0 (SB l b) (QB l b)

/-- The loader's facts as the builders take them. -/
structure Ld : Prop where
  pg : o.prog = wakeProg
  lo : (Ly).Λ.code.lo = Spike.Lib.A64.WakePh.lo
  lab : ∀ l x, Scc.Cert.Link.A64.codeOf Spike.Lib.A64.WakePh.lo wakeProg l = some x → (Ly).lab l = Int64.ofNat x
  Λ : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName
  site : (Spike.Lib.A64.PhRec.μ (Ly)).site .take =
    some ((Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat
  E : (Ly).endPc = WakeSpawnR.endR hp i
  pa : Scc.Sem.A64.textProgram SccCertificate.asm = .ok o.prog

/-- `Ld` from the loader's facts. -/
theorem ld_of (hpa : Scc.Sem.A64.textProgram SccCertificate.asm = .ok o.prog)
    (hwp : Scc.Sem.A64.textProgram SccCertificate.asm = .ok wakeProg)
    (hlo0 : Λ0.code.lo = Spike.Lib.A64.WakePh.lo) : Ld hp i := by
  have hpg := WakeSrcCtl.oprog_W hpa hwp
  have hlo := Spike.Lib.A64.WakePh.StartPlaceLy.hlo_W hp i hlo0
  exact ⟨hpg, hlo, fun l x h => Spike.Lib.PlaceW.hlab_ofPlaceW hp i l x (by rw [hlo, hpg]; exact h),
    Spike.Lib.PlaceW.abortLbl_of_placeW (Spike.Lib.PlaceW.link i hp), Spike.Lib.PlaceW.site_ofPlaceW hp i,
    by show Scc.Cert.Rt.A64.endOf _ (Ly).prog _ = _; rw [WakeSrcCtl.prog_W hp i hpa hwp], hpa⟩

/-- `.L21_wc_main.sp0` at the canonical base. -/
theorem lab_sp0 (hd : Ld hp i) : (Ly).lab ".L21_wc_main.sp0" = Int64.ofNat 2169224 :=
  hd.lab _ _ (by rw [← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel)

set_option maxHeartbeats 1600000 in
/-- **`bl` inside `W1W`**: the reserve's call block (`WcWf.blkW_wfC`). -/
theorem bl_W1 (hd : Ld hp i) {l : WeakMem.AllocLabel} {b n : Nat} {R : Region} {F : MachineData → Prop}
    {J0 : AS → Ctl → Prop} {t : UInt64} (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -336)
    (hhi : 0 ≤ R.hi) (hst : STW) (hpl : PLW) :
    BlkW Wq (fun _ _ => False) (Ly).exe (WakeSpawnR.endR hp i) R F (rN (tpXa ms1 t) LB J0 (SB l b) .bl) resB := by
  have hW := Spike.Lib.A64.WakePh.WcWf.blkW_wfC (L := Ly) (a := ntA (Ly).lab) (Dt := Dt) (ar := WakeOD.arW hp i)
    (p := WakeT1.wakeSrc) (Cl := WakeOD.ClW hp i) (Ctx := fun _ _ _ => False)
    (lsize := A64ConsumerA.updN (WakeLoadT.ls0T ls0) l n) (fs := []) hd.pg hd.lo hd.lab hd.site
    (l := ".L21_wc_main.sp0") (k := 5)
    (by have := wake_wcResIn; simp only [wcResIn, Bool.and_eq_true] at this; exact this.1.2)
    rfl resB_ok hR hal (by omega) (by omega)
    (Spike.Lib.A64.WakePh.CalWf.blkW_noK hst.res.bl fun _ _ h => h) ?_ (by decide +kernel) (by decide)
    (fun _ h => h.2) (fun σ c ⟨_, _, hS, _⟩ => ⟨fun _ => (WakeSrcCtl.spawnSrc_ctl hS.2.2).1,
      (WakeSrcCtl.spawnSrc_ctl hS.2.2).2⟩) hpl.bl
  · rw [← hd.E]
    unfold WakeOPremW.W1W Spike.Lib.A64.WakeWf.W1 WakeOD.AbW WakeOD.AcW
    rw [Spike.Lib.A64.Flow.Worker.Wake.AbOffW.marks_target (Ly) hd.pa]
    exact Spike.Lib.A64.WakePh.CalWf.blkW_noK hW fun _ _ h => h
  · intro j hj; rw [Spike.Lib.A64.WakePh.okPc_eq hd.Λ]
    show Spike.Lib.A64.WakePh.okC ((Ly).lab ".L21_wc_main.sp0" + _ + _).toBitVec.toNat = true
    rw [lab_sp0 hp i hd]; revert j; decide

set_option maxHeartbeats 1600000 in
/-- **A covered `ret`-free block of `wc_main` inside `W1W`** (`WcWf.blkW_wfC`
at `ofPlaceW`): at label `lb` (at `P`), offset `k`, its pcs `okC` there
(`hokP`), its controls `SpawnSrc` ones (`hJ`). -/
theorem blkG (hd : Ld hp i) {l : WeakMem.AllocLabel} {b n : Nat} {R : Region} {F : MachineData → Prop}
    {K' : State → State → Prop} {nd : ND} {blk : List Directive} {lb : String} {k P : Nat}
    (hb : Scc.Cert.Rt.A64.blockAt wakeProg lb k blk = true) (he : (Ly).lab lb + Int64.ofNat (4 * k) = nd.pc)
    (hlb : (Ly).lab lb = Int64.ofNat P) (hok : Spike.Lib.A64.Flow.okBlk (-80) 0 nd.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -336) (hhi : 0 ≤ R.hi)
    (hst : BlkW (fun s _ => SFactsSt2 (Ly).Λ (Spike.Lib.A64.PhRec.μ (Ly)) (ownG (Ly) (ntA (Ly).lab)) s) K'
      (Ly).exe (Ly).endPc R F nd blk)
    (hokP : ∀ j < blk.length,
      Spike.Lib.A64.WakePh.okC (Int64.ofNat P + Int64.ofNat (4 * k) + Int64.ofNat (4 * j)).toBitVec.toNat = true)
    (hph : Spike.Lib.A64.WakeWf.phOffW Spike.Lib.A64.Flow.Worker.Wake.Child.pfxM lb k lb blk = true)
    (hnr : Spike.Lib.A64Consumer.noRetBlk blk = true)
    (hJ : ∀ σ c, nd.J σ c → ∃ l' A', SB l b l' A' c)
    (hpl : BlkW (fun s c => Spike.Lib.A64ConsumerS.PlacedSE (Ly).Λ (Spike.Lib.A64.WakePh.PlacedLy.lblL (Ly).Λ l b)
      s c []) (fun _ _ => False) (Ly).exe (Ly).endPc R F nd blk) :
    BlkW Wq (fun _ _ => False) (Ly).exe (WakeSpawnR.endR hp i) R F nd blk := by
  have hpc : nd.pc = Int64.ofNat P + Int64.ofNat (4 * k) := by rw [← he, hlb]
  have hW := Spike.Lib.A64.WakePh.WcWf.blkW_wfC (L := Ly) (a := ntA (Ly).lab) (Dt := Dt) (ar := WakeOD.arW hp i)
    (p := WakeT1.wakeSrc) (Cl := WakeOD.ClW hp i) (Ctx := fun _ _ _ => False)
    (lsize := A64ConsumerA.updN (WakeLoadT.ls0T ls0) l n) (fs := []) hd.pg hd.lo hd.lab hd.site hb he hok
    hR hal (by omega) (by omega) hst (fun j hj => by rw [Spike.Lib.A64.WakePh.okPc_eq hd.Λ, hpc]; exact hokP j hj)
    hph hnr (fun _ h => h.2)
    (fun σ c h => by
      obtain ⟨_, _, hS⟩ := hJ σ c h
      exact ⟨fun _ => (WakeSrcCtl.spawnSrc_ctl hS.2.2).1, (WakeSrcCtl.spawnSrc_ctl hS.2.2).2⟩) hpl
  rw [← hd.E]
  unfold WakeOPremW.W1W Spike.Lib.A64.WakeWf.W1 WakeOD.AbW WakeOD.AcW
  rw [Spike.Lib.A64.Flow.Worker.Wake.AbOffW.marks_target (Ly) hd.pa]
  exact Spike.Lib.A64.WakePh.CalWf.blkW_noK hW fun _ _ h => h

/-- `.L21_wc_main.sp3`, `.sp4`, `.sp6` at the canonical base. -/
theorem labs (hd : Ld hp i) : (Ly).lab ".L21_wc_main.sp3" = Int64.ofNat 2169248 ∧
    (Ly).lab ".L21_wc_main.sp4" = Int64.ofNat 2169268 ∧ (Ly).lab ".L21_wc_main.sp6" = Int64.ofNat 2169292 :=
  ⟨hd.lab _ _ (by rw [← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel),
    hd.lab _ _ (by rw [← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel),
    hd.lab _ _ (by rw [← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel)⟩

set_option maxHeartbeats 1600000 in
/-- **`wc_main`'s blocks past `.sp3` inside `W1W`** (`blkG` at each). -/
theorem blks_W1 (hd : Ld hp i) {l : WeakMem.AllocLabel} {b n : Nat} {R : Region} {F : MachineData → Prop}
    {J0 : AS → Ctl → Prop} {t : UInt64} (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -336)
    (hhi : 0 ≤ R.hi) (hst : STW) (hpl : PLW) (c0 : Ctl) (cA m : BitVec 64) (fr : BitVec 64 × BitVec 64) (hM : MG) :
    BlkW Wq (fun _ _ => False) (Ly).exe (WakeSpawnR.endR hp i) R F (wcN3 LB (j3 cA m fr) c0) tcb2Call ∧
    BlkW Wq (fun _ _ => False) (Ly).exe (WakeSpawnR.endR hp i) R F (aN LB c0 (t2 LB) cA m fr .n4) sp4A ∧
    BlkW Wq (fun _ _ => False) (Ly).exe (WakeSpawnR.endR hp i) R F (aN LB c0 (t2 LB) cA m fr .n5) initCall ∧
    BlkW Wq (fun _ _ => False) (Ly).exe (WakeSpawnR.endR hp i) R F (bN LB c0 (t2 LB) cA m fr .n6) sp6A ∧
    BlkW Wq (fun _ _ => False) (Ly).exe (WakeSpawnR.endR hp i) R F (bN LB c0 (t2 LB) cA m fr .n6a) cloneArgs := by
  obtain ⟨e3, e4, e6⟩ := labs hp i hd
  obtain ⟨l', A', hS, -⟩ := hM.1
  have hin := Spike.Lib.A64.WakePh.WcSp4W.sp4In
  have h3 := Spike.Lib.A64.WakePh.Tcb2Call.wake_tcb2CallIn
  simp only [Spike.Lib.A64.WakePh.Tcb2Call.tcb2CallIn, Bool.and_eq_true] at h3
  have hc : ∀ c, c = c0 → ∃ l' A', SB l b l' A' c := fun c e => ⟨l', A', e ▸ hS⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact blkG hp i E Dt Ctx ls0 hd h3.1 (Spike.Lib.A64.Flow.ofNat4_zero _) e3
      Spike.Lib.A64.WakePh.Tcb2Call.tcb2Call_ok hR hal hRlo hhi (hst.sp3 c0 cA m fr hM).blk (by decide)
      (by decide +kernel) (by decide) (fun _ _ h => hc _ h.1) (hpl.sp3 c0 cA m fr hM)
  · exact blkG hp i E Dt Ctx ls0 hd hin.1 (Spike.Lib.A64.Flow.ofNat4_zero _) e4
      Spike.Lib.A64.WakePh.WcSp4.sp4A_ok hR hal hRlo hhi (hst.sp4 c0 cA m fr hM).n4 (by decide)
      (by decide +kernel) (by decide) (fun _ _ h => hc _ h.1.1) (hpl.n4 c0 cA m fr hM)
  · exact blkG hp i E Dt Ctx ls0 hd hin.2.2.1 rfl e4
      Spike.Lib.A64.WakePh.WcSp4.initCall_ok hR hal hRlo hhi (hst.sp4 c0 cA m fr hM).n5 (by decide)
      (by decide +kernel) (by decide) (fun _ _ h => hc _ h.1) (hpl.n5 c0 cA m fr hM)
  · exact blkG hp i E Dt Ctx ls0 hd hin.2.2.2.1 (Spike.Lib.A64.Flow.ofNat4_zero _) e6
      Spike.Lib.A64.WakePh.WcSp4.sp6A_ok hR hal hRlo hhi (hst.sp4 c0 cA m fr hM).n6 (by decide)
      (by decide +kernel) (by decide) (fun _ _ h => hc _ h.1) (hpl.n6 c0 cA m fr hM)
  · exact blkG hp i E Dt Ctx ls0 hd hin.2.2.2.2.2 rfl e6
      Spike.Lib.A64.WakePh.WcSp4.cloneArgs_ok hR hal hRlo hhi (hst.sp4 c0 cA m fr hM).n6a (by decide)
      (by decide +kernel) (by decide) (fun _ _ h => hc _ h.1) (hpl.n6a c0 cA m fr hM)

/-! ## Single instructions -/

section Box

open CoreLang CoreTerm

/-- The three terms of main's source from the box to the spawn. -/
def BoxT (t : Expr) : Prop :=
  t = boxTerm ∨ t = .let_ "p" (.pair (.var "c") (.var "me")) Spike.Lib.WakePreA.spawnTerm ∨
    t = Spike.Lib.WakePreA.spawnTerm

/-- Main's source runs from the box only through `BoxT`, at no frame. -/
theorem boxT_run {p : Prog} {q q' : Ctl × List TermRun.Frame} (h : FrameRun p q q') (ht : BoxT q.1.term)
    (hf : q.2 = []) : BoxT q'.1.term ∧ q'.2 = [] := by
  induction h with
  | refl => exact ⟨ht, hf⟩
  | step hs _ ih =>
    refine ih ?_ ?_
    all_goals cases hs with
    | loc hl =>
      first
      | exact hf
      | rcases ht with ht | ht | ht
        · exact .inr (.inl (Spike.Lib.Hello1Runs.localStepS_let hl ht (by intros; simp) (by intros; simp)))
        · exact .inr (.inr (Spike.Lib.Hello1Runs.localStepS_let hl ht (by intros; simp) (by intros; simp)))
        · have e := Spike.Lib.WakeSrcCtl.frameRun_spawn ht (.single (.loc hl (fs := [])))
          cases e; exact .inr (.inr ht)
    | call hc => rcases ht with ht | ht | ht <;> rw [ht] at hc <;> simp [boxTerm, Spike.Lib.WakePreA.spawnTerm] at hc
    | ret hc => simp at hf

/-- **The box's control** is not at a `ret` and its runs are well formed. -/
theorem boxT_runWf {p : Prog} {c : Ctl} (ht : c.term = boxTerm) :
    (∀ a, c.term ≠ .ret a) ∧ Spike.Lib.A64.WakeWf.RunWf p c [] := by
  refine ⟨fun a e => by rw [ht] at e; simp [boxTerm] at e, ⟨?_, ?_⟩⟩
  · intro c' fs' hr x a e ty w hc
    have h := (boxT_run hr (.inl ht) rfl).1
    rcases hc with hc | ⟨b, hc⟩ <;> rcases h with h | h | h <;> rw [hc] at h <;>
      simp [boxTerm, Spike.Lib.WakePreA.spawnTerm] at h
  · intro c' fs' hr x a τ e hc
    have h := (boxT_run hr (.inl ht) rfl).1
    rcases h with h | h | h <;> rw [hc] at h <;> simp [boxTerm, Spike.Lib.WakePreA.spawnTerm] at h

end Box

set_option maxHeartbeats 1600000 in
/-- **A silent single instruction of `wc_main` writing nothing inside `W1W`**
(`WcWf.nodeW_wfC` at `ofPlaceW`): its cell steps to `pc + 4` and writes
nothing (`hcell`), it is no `svc` (`hsvc`). -/
theorem nodeG (hd : Ld hp i) {l : WeakMem.AllocLabel} {b n : Nat} {R : Region} {F : MachineData → Prop}
    {K' : State → State → Prop} {nd : ND} {d : Directive} {lb : String} {k P : Nat}
    (hb : Scc.Cert.Rt.A64.blockAt wakeProg lb k [d] = true) (he : (Ly).lab lb + Int64.ofNat (4 * k) = nd.pc)
    (hlb : (Ly).lab lb = Int64.ofNat P)
    (hcell : ∀ s, Kraken.Promising.Lower.A64.CellAt s d 4 → (∃ tree, isaLSE2.exec s = some tree ∧
      ∀ s', Scc.Sem.TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat 4) ∧ ∀ L, ¬ A64ConsumerA.WrAt s L)
    (hsvc : ∀ imm, d ≠ .instr ⟨.W64, .SVC imm⟩)
    (hst : NodeW (fun s _ => SFactsSt2 (Ly).Λ (Spike.Lib.A64.PhRec.μ (Ly)) (ownG (Ly) (ntA (Ly).lab)) s) K'
      (Ly).exe (Ly).endPc R F nd)
    (hokP : Spike.Lib.A64.WakePh.okC (Int64.ofNat P + Int64.ofNat (4 * k)).toBitVec.toNat = true)
    (hph : Spike.Lib.A64.WakeWf.siOffW Spike.Lib.A64.Flow.Worker.Wake.Child.pfxM lb k = true)
    (hJ : ∀ σ c, nd.J σ c → (∀ a, c.term ≠ .ret a) ∧ Spike.Lib.A64.WakeWf.RunWf WakeT1.wakeSrc c [])
    (hpl : NodeW (fun s c => Spike.Lib.A64ConsumerS.PlacedSE (Ly).Λ (Spike.Lib.A64.WakePh.PlacedLy.lblL (Ly).Λ l b)
      s c []) (fun _ _ => False) (Ly).exe (Ly).endPc R F nd) :
    NodeW Wq (fun _ _ => False) (Ly).exe (WakeSpawnR.endR hp i) R F nd := by
  have hpc : nd.pc = Int64.ofNat P + Int64.ofNat (4 * k) := by rw [← he, hlb]
  have hok : Spike.Lib.A64.WakePh.okC nd.pc.toBitVec.toNat = true := by rw [hpc]; exact hokP
  have hc : ∀ s c, At (Ly).exe (Ly).endPc R F nd s c → Kraken.Promising.Lower.A64.CellAt s d 4 :=
    fun s c ⟨h1, h2, _, h4, _⟩ => Spike.Lib.A64.WakePh.WcW.cell1 hd.pg hb h1 h2 (by rw [h4, he])
  have hW := Spike.Lib.A64.WakePh.WcWf.nodeW_wfC (L := Ly) (a := ntA (Ly).lab) (Dt := Dt) (ar := WakeOD.arW hp i)
    (p := WakeT1.wakeSrc) (Cl := WakeOD.ClW hp i) (Ctx := fun _ _ _ => False)
    (lsize := A64ConsumerA.updN (WakeLoadT.ls0T ls0) l n) (fs := []) hd.pg hd.lo hd.lab he hst
    (Spike.Lib.A64.WakePh.CalWf.htkC hd.lab hd.site hok) (by rw [Spike.Lib.A64.WakePh.okPc_eq hd.Λ]; exact hok)
    hph (fun s c hA => by
      obtain ⟨⟨tree, h1, h2⟩, -⟩ := hcell s (hc s c hA)
      exact ⟨d, tree, hc s c hA, hsvc, h1, h2⟩)
    (fun _ h => h.2) (fun σ c h => ⟨fun _ => (hJ σ c h).1, (hJ σ c h).2⟩) hpl
    (Spike.Lib.A64.WakeWf.nodeW_noWrC fun s c hA => ⟨(hcell s (hc s c hA)).2, fun _ h => h⟩)
  rw [← hd.E]
  unfold WakeOPremW.W1W Spike.Lib.A64.WakeWf.W1 WakeOD.AbW WakeOD.AcW
  rw [Spike.Lib.A64.Flow.Worker.Wake.AbOffW.marks_target (Ly) hd.pa]
  exact Spike.Lib.A64.WakePh.CalWf.nodeW_noK hW fun _ _ h => h

/-- A fence's cell steps to `pc + 4`, writing nothing. -/
theorem dmb_cell {fk : FenceKind} (s : State)
    (hc : Kraken.Promising.Lower.A64.CellAt s (.instr ⟨.W64, .DMB fk⟩) 4) :
    (∃ tree, isaLSE2.exec s = some tree ∧ ∀ s', Scc.Sem.TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat 4) ∧
      ∀ L, ¬ A64ConsumerA.WrAt s L := by
  refine ⟨⟨_, Kraken.Promising.Lower.A64.exec_dmb hc, fun s' hu => ?_⟩, ?_⟩
  · obtain ⟨_, hu⟩ := hu
    simp only [Scc.Sem.TreeLeaf] at hu
    subst hu; rfl
  · rintro L (⟨_, _, _, h⟩ | ⟨_, _, _, h⟩) <;> rw [Kraken.Promising.Lower.A64.exec_dmb hc] at h <;> cases h

/-- A register-only instruction's cell steps to `pc + 4`, writing nothing. -/
theorem reg_cell {w : RegWidth} {op : Operation w} (hop : Spike.Lib.A64.Flow.RegOnly op = true) (s : State)
    (hc : Kraken.Promising.Lower.A64.CellAt s (.instr ⟨w, op⟩) 4) :
    (∃ tree, isaLSE2.exec s = some tree ∧ ∀ s', Scc.Sem.TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat 4) ∧
      ∀ L, ¬ A64ConsumerA.WrAt s L :=
  ⟨⟨_, Spike.Lib.A64.Flow.exec_reg hop hc, fun s' hl => by cases hl; rfl⟩,
    A64ConsumerA.noWr_done (Spike.Lib.A64.Flow.exec_reg hop hc)⟩

set_option maxHeartbeats 1600000 in
/-- **`wc_main`'s single instructions inside `W1W`**: the fences `f`, `n6f`
and `scc_rt_thread_init`'s `sub` (`nodeG`), the tid store `n4s`
(`CalWf.nodeCst`, its word unmapped under `F` by `htidW`, off the arena by
`hoffT_W`). -/
theorem nodes_W1 (hd : Ld hp i) (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (hcz : Spike.Lib.A64.Rt.CtrZ o) {l : WeakMem.AllocLabel} {b n : Nat} {R : Region} {F : MachineData → Prop}
    {J0 : AS → Ctl → Prop} {t : UInt64} (hst : STW) (hpl : PLW)
    (htid : ∀ m', F m' → Mem.loadInt m'.dmem (t2 (Ly).lab + 56#64) 8 = none) :
    NodeW Wq (fun _ _ => False) (Ly).exe (WakeSpawnR.endR hp i) R F (rNQ (tpXa ms1 t) LB J0 (SB l b) (QB l b) .f) ∧
    ∀ c0 cA m fr, MG →
      NodeW Wq (fun _ _ => False) (Ly).exe (WakeSpawnR.endR hp i) R F (aN LB c0 (t2 LB) cA m fr .n4s) ∧
      NodeW Wq (fun _ _ => False) (Ly).exe (WakeSpawnR.endR hp i) R F (wcNI LB c0 (t2 LB) cA m fr) ∧
      NodeW Wq (fun _ _ => False) (Ly).exe (WakeSpawnR.endR hp i) R F (bN LB c0 (t2 LB) cA m fr .n6f) := by
  obtain ⟨-, e4, e6⟩ := labs hp i hd
  have hin := Spike.Lib.A64.WakePh.WcSp4W.sp4In
  refine ⟨?_, fun c0 cA m fr hM => ?_⟩
  · have h4 := wake_wcResIn
    simp only [wcResIn, Bool.and_eq_true] at h4
    have hf := h4.1.1
    rw [pubF_eq] at hf
    exact nodeG hp i E Dt Ctx ls0 hd hf rfl (lab_sp0 hp i hd) (dmb_cell (fk := .st)) (fun _ h => by cases h)
      (Spike.Lib.A64.WakePh.CalWf.nodeW_noK hst.res.f fun _ _ h => h) (by decide) (by decide +kernel)
      (fun σ c ⟨_, _, _, hq⟩ => boxT_runWf hq.2.2.1) hpl.f
  obtain ⟨l', A', hS, -⟩ := hM.1
  have hc : ∀ c, c = c0 → (∀ a, c.term ≠ .ret a) ∧ Spike.Lib.A64.WakeWf.RunWf WakeT1.wakeSrc c [] :=
    fun c e => e ▸ WakeSrcCtl.spawnSrc_ctl hS.2.2
  have hs4 := hst.sp4 c0 cA m fr hM
  refine ⟨?_, ?_, ?_⟩
  · have hW := Spike.Lib.A64.WakePh.CalWf.nodeCst (L := Ly) (own := ownG (Ly) (ntA (Ly).lab)) (Dt := Dt)
      (ar := WakeOD.arW hp i) (p := WakeT1.wakeSrc) (Cl := WakeOD.ClW hp i) (Ctx := fun _ _ _ => False)
      (lsize := A64ConsumerA.updN (WakeLoadT.ls0T ls0) l n) (fs := []) hd.pg hd.lo hd.Λ hd.lab hd.site
      (fun _ h => h.2) hin.2.1 rfl hs4.n4s
      (by show Spike.Lib.A64.WakePh.okC ((Ly).lab _ + _).toBitVec.toNat = true; rw [e4]; decide)
      (by decide +kernel) (fun σ c h => ⟨fun _ => (hc c h.1.1).1, (hc c h.1.1).2⟩)
      (hpl.n4s c0 cA m fr hM)
      (fun σ c m' h hm => by
        rw [Spike.Lib.A64.Flow.Ret0.rAddr_x10 h.1.2.2.1,
          show BitVec.ofInt 64 (56 : Int64).toInt = 56#64 from by decide]
        exact htid m' hm)
      (fun σ c m' h _ => by
        rw [Spike.Lib.A64.Flow.Ret0.rAddr_x10 h.1.2.2.1,
          show BitVec.ofInt 64 (56 : Int64).toInt = 56#64 from by decide]
        exact Spike.Lib.A64.WakePh.CalWf.hoffT_W hp i hpin2 hcz)
    rw [← hd.E]
    unfold WakeOPremW.W1W Spike.Lib.A64.WakeWf.W1 WakeOD.AbW WakeOD.AcW
    rw [Spike.Lib.A64.Flow.Worker.Wake.AbOffW.marks_target (Ly) hd.pa]
    exact Spike.Lib.A64.WakePh.CalWf.nodeW_noK hW fun _ _ h => h
  · exact nodeG hp i E Dt Ctx ls0 hd Spike.Lib.A64.WakePh.WcSp4W.wake_tiSub (Spike.Lib.A64.Flow.ofNat4_zero _)
      (Spike.Lib.A64.WakePh.WcSp4W.lab_ti hd.lab) (reg_cell (by decide)) (fun _ h => by cases h) hs4.nI
      (by decide) (by decide +kernel) (fun σ c h => hc c h.1) (hpl.nI c0 cA m fr hM)
  · exact nodeG hp i E Dt Ctx ls0 hd hin.2.2.2.2.1 rfl e6 (dmb_cell (fk := .sy)) (fun _ h => by cases h) hs4.n6f
      (by decide) (by decide +kernel) (fun σ c h => hc c h.1) (hpl.n6f c0 cA m fr hM)

/-! ## `H1G.wcWf` -/

set_option maxHeartbeats 1600000 in
/-- **`H1G.wcWf`**: `wc_main`'s own nodes inside `W1W … l b n`, at one
ghost of `Box` (`hB`, `l` fresh in the start's labels, `hl`), from the
loader's facts and the per-node word premises of `WcMidWG.wcMidW_wcG`
(`hb`, `hhdr`, `hmP`, `hmH`, `hband`, `htidW`) and `H1G`'s `hunN`, `hunP`,
`hunH`. -/
theorem wcMainW_wf (hpa : Scc.Sem.A64.textProgram SccCertificate.asm = .ok o.prog)
    (hwp : Scc.Sem.A64.textProgram SccCertificate.asm = .ok wakeProg)
    (hlo0 : Λ0.code.lo = Spike.Lib.A64.WakePh.lo)
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size) (hcz : Spike.Lib.A64.Rt.CtrZ o)
    {l : WeakMem.AllocLabel} {b n : Nat} {F0 : MachineData → Prop} {R : Region} {F : MachineData → Prop}
    {J0 : AS → Ctl → Prop} {t : UInt64} (hB : BoxPure (Ly) F0 n R F J0 t)
    (hl : Spike.Lib.WakeLoadT.L0T (Ly).Λ l = none)
    (hunN : ∀ m, F m → Mem.loadInt m.dmem (ntA (Ly).lab) 8 = none)
    (hb : Spike.Lib.A64.WakePh.Tcb2CallW.BandSp3 (Ly) R)
    (hhdr : (Ly).pinA + 80#64 + 16#64 ∉ [(Ly).pnA, (Ly).lockA, (Ly).freeNA, (Ly).nextA, ntA (Ly).lab])
    (hmP : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 (Ly).Λ) true ⟨(Ly).pnA, 8⟩ = true)
    (hmH : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 (Ly).Λ) true ⟨(Ly).pinA + 96#64, 8⟩ = true)
    (hunP : ∀ m, F m → Mem.loadInt m.dmem (Ly).pnA 8 = none)
    (hunH : ∀ m, F m → Mem.loadInt m.dmem ((Ly).pinA + 96#64) 8 = none)
    (hband : Spike.Lib.A64.WakePh.WcSp4W.BandTi (Ly) R)
    (htidW : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 (Ly).Λ) true ⟨t2 (Ly).lab + 56#64, 8⟩ = true ∧
      (∀ m', F m' → Mem.loadInt m'.dmem (t2 (Ly).lab + 56#64) 8 = none) ∧
      ∀ w, (⟨t2 (Ly).lab + 56#64, 8⟩, w) ∉ Spike.Lib.A64.WakePh.own2a (Ly) (ntA (Ly).lab) 0) :
    WcMainW Wq (fun _ _ => False) (Ly).exe (WakeSpawnR.endR hp i) R F F (tpXa ms1 t) J0 (SB l b) (QB l b) := by
  have hd := ld_of hp i hpa hwp hlo0
  have hst := wcMidW_st hp i E cT ls0 hpa hwp hlo0 hA13 (l := l) (b := b) (n := n) hB hunN hb hhdr hmP hmH
    hunP hunH hband htidW
  have hpl : PLW := Spike.Lib.A64.WakePh.PlacedLy.wcMainW_placed hB hl
  obtain ⟨⟨hR, hal, -, hRlo, hhi, -, -⟩, -⟩ := hB
  have hN := nodes_W1 hp i E cT Dt Ctx ls0 hd hpin2 hcz hst hpl htidW.2.1
  have hK := blks_W1 hp i E cT Dt Ctx ls0 hd hR hal hRlo hhi hst hpl
  exact wcMainW_W1 hp i E cT Dt Ctx ls0 hN.1 (bl_W1 hp i E cT Dt Ctx ls0 hd hR hal hRlo hhi hst hpl)
    (fun c0 cA m fr h => (hK c0 cA m fr h).1) (fun c0 cA m fr h => (hK c0 cA m fr h).2.1)
    (fun c0 cA m fr h => (hN.2 c0 cA m fr h).1) (fun c0 cA m fr h => (hK c0 cA m fr h).2.2.1)
    (fun c0 cA m fr h => (hN.2 c0 cA m fr h).2.1) (fun c0 cA m fr h => (hK c0 cA m fr h).2.2.2.1)
    (fun c0 cA m fr h => (hN.2 c0 cA m fr h).2.2) (fun c0 cA m fr h => (hK c0 cA m fr h).2.2.2.2)

/-! ## The bands from `BoxPure` -/

/-- **`wcMainW_wf`'s stack bands from the box** (`hb`, `hband`): `BandTi`
is `BoxPure`'s band; `BandSp3`'s callee band (`[-272, -80]`) lies in the
first stack `[stacksA, stacksA + 16384)` (`R.base + 48 = stacksA + 16384`),
inside the pool (`stacks_sub`). -/
theorem bands_of_box {L : Spike.Lib.A64.Rt.RuntimeLayout} {F0 : MachineData → Prop} {n : Nat} {R : Region}
    {F : MachineData → Prop} {J0 : AS → Ctl → Prop} {t : UInt64} (hB : BoxPure L F0 n R F J0 t) :
    Spike.Lib.A64.WakePh.Tcb2CallW.BandSp3 L R ∧ Spike.Lib.A64.WakePh.WcSp4W.BandTi L R := by
  obtain ⟨⟨hR, -, -, hRlo, hhi, -, -⟩, hband, -, ⟨-, -, hst⟩, -⟩ := hB
  refine ⟨fun k h1 h2 => ?_, hband⟩
  have hs := L.stacks_sub
  simp only [Scc.Sem.Range.Sub] at hs
  have e := Region.addr_toNat_of hR (k := -80 + k) (by omega) (by omega)
  rw [Region.callee_addr]
  omega

end Spike.Lib.WakeWcW1I

/-- info: 'Spike.Lib.WakeWcW1I.wcMainW_W1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeWcW1I.wcMainW_W1

/-- info: 'Spike.Lib.WakeWcW1I.wcMidW_st' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeWcW1I.wcMidW_st

/-- info: 'Spike.Lib.WakeWcW1I.bl_W1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeWcW1I.bl_W1

/-- info: 'Spike.Lib.WakeWcW1I.blkG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeWcW1I.blkG

/-- info: 'Spike.Lib.WakeWcW1I.blks_W1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeWcW1I.blks_W1

/-- info: 'Spike.Lib.WakeWcW1I.boxT_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeWcW1I.boxT_run

/-- info: 'Spike.Lib.WakeWcW1I.boxT_runWf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeWcW1I.boxT_runWf

/-- info: 'Spike.Lib.WakeWcW1I.nodeG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeWcW1I.nodeG

/-- info: 'Spike.Lib.WakeWcW1I.dmb_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeWcW1I.dmb_cell

/-- info: 'Spike.Lib.WakeWcW1I.reg_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeWcW1I.reg_cell

/-- info: 'Spike.Lib.WakeWcW1I.nodes_W1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeWcW1I.nodes_W1

/-- info: 'Spike.Lib.WakeWcW1I.wcMainW_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeWcW1I.wcMainW_wf

/-- info: 'Spike.Lib.WakeWcW1I.bands_of_box' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeWcW1I.bands_of_box
