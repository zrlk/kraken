/-
**`RefBlk`: the refusal path's three blocks inside `W1X`** (AArch64,
wake.w): `cb`, `.clone9`'s `cl` and `.1_spawnfail5`'s `flB`, between
`.sp6 + 56` and `.sp6 + 88`, inside `W1W` (`WakeWf.blkW_wf`: `SFactsSt2` at
`ownG` by `WcSp4W.blk_c` at `own2b … 0`, where `ownG` agrees with it,
`agreeBlk`; the write abort by `blkW_dispAbI`; the blocks inside the threads
abort phase `Ac`, `ac_cb`/`ac_cl`/`ac_fl`) and `X1W` (off the clone's `svc` and the take site), under no
`K1W` move (`takeCKS_none`).

- `atL`, `of_atL`: a property of a label's address, decided on `codeT`.
- `blkFacts`: the blocks' pcs, `ph2b` `0` and off the sites there.
- `blk1`: one block; `refBlk`: the piece (`hl`: `l` is not a static label).
-/
import Spike.Lib.A64WakeRefAbW
import Spike.Lib.A64WakeWfCal
import Spike.Lib.A64WakeWcSp4W
import Spike.Lib.A64SpawnFailAC
import Spike.Lib.A64WakeRefAg
import Spike.Lib.A64WakeRefAb
import Spike.Lib.A64WakeRefPh
import Spike.Lib.A64WakeWfN

namespace Spike.Lib.WakeRefStub

open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib (Region FragS)
open Spike.Lib.A64.Flow (ND BlkW DFrame Abs arun)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.WakePh (lo ownG own2b ph2bC okC)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Flow.Worker.Wake.Child (pfxM)
open Spike.Lib.A64.Flow.Worker.Wake.SpawnFail (fN MS flB_ok flB_noRet flB_run cb_noRet cl_noRet ofInt_add8 subs0_lt ac_cb ac_cl ac_fl)
open Spike.Lib.A64.Flow.Worker.Wake.Parent (cbP_ok cl_ok cbP_run cbPT_run cl_run clT_run)
open Spike.Lib.WakeRefSeg (W1X)
open Spike.Lib.WakeH1Inv (K1W)
open Spike.Lib.WakeSpawnR (endR)

/-- A property `p` of label `l`'s address, decided on `codeT`. -/
def atL (l : String) (p : Nat → Bool) : Bool :=
  match Scc.Cert.Rt.A64.codeT lo wakeProg l with
  | some x => p x
  | none => false

theorem of_atL {l : String} {p : Nat → Bool} (h : atL l p = true) :
    ∃ x, codeOf lo wakeProg l = some x ∧ p x = true := by
  unfold atL at h; rw [Scc.Cert.Rt.A64.codeT_eq] at h
  split at h
  · next x hx => exact ⟨x, hx, h⟩
  · cases h

/-- **The refusal blocks' pcs**: `.clone9` at `.sp6 + 60`, `.1_spawnfail5`
at `.sp6 + 84`, the nine pcs from `.sp6 + 56` below `.stack_grow` with
`ph2b` `0` and off the sites, the take site below `.sp6`; `scc_rt_abort`
at `ph2b` `0`, below `scc_rt_thr_worker`. -/
def blkFacts : Bool :=
  atL ".L21_wc_main.sp6" (fun x => decide (x + 100 < 2 ^ 63) &&
    atL (pfxM ++ ".clone9") (fun y => y == x + 60) && atL (pfxM ++ ".1_spawnfail5") (fun y => y == x + 84) &&
    atL ".L21_wc_main.stack_grow" (fun y => decide (x + 88 < y ∧ y < 2 ^ 63)) &&
    atL Spike.Lib.A64.Flow.Ret0.StackTake.siteL (fun y => decide (y < x)) &&
    (List.range 9).all fun j => ph2bC (x + 56 + 4 * j) == 0 && okC (x + 56 + 4 * j)) &&
  atL "scc_rt_abort" (fun x => ph2bC x == 0 && decide (x < 2 ^ 63) &&
    atL "scc_rt_thr_worker" (fun y => decide (x < y ∧ y < 2 ^ 63)))

theorem blkFacts_ok : blkFacts = true := by decide +kernel

theorem toNat_lab {lab : Label → Int64} (hlab : ∀ l x, codeOf lo wakeProg l = some x → lab l = Int64.ofNat x)
    {l : Label} {x : Nat} (h : codeOf lo wakeProg l = some x) (hx : x < 2 ^ 64) : (lab l).toBitVec.toNat = x := by
  rw [hlab l x h]; show (BitVec.ofNat 64 x).toNat = x; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]

theorem toNat_off (x k : Nat) (h : x + k < 2 ^ 64) : (Int64.ofNat x + Int64.ofNat k).toBitVec.toNat = x + k := by
  rw [Spike.Lib.A64.Rt.PhOfTab.toNat_add, Nat.mod_eq_of_lt h]

theorem toNat_ofNat {x : Nat} (h : x < 2 ^ 64) : (Int64.ofNat x).toBitVec.toNat = x := by
  show (BitVec.ofNat 64 x).toNat = x; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (Dt : State → Prop) (Ctx : FragS isaLSE2) (ls0 : Spike.Lib.A64Consumer.Lsize)

set_option hygiene false in
/-- The layout of `ofPlaceW`. -/
local notation "Ly" => RuntimeLayout.ofPlaceW hp i

set_option hygiene false in
/-- The owned words' counter address. -/
local notation "aN" => Spike.Lib.A64.Rt.Reserve.ntA (RuntimeLayout.ofPlaceW hp i).lab

/-- **One refusal block inside `W1X`**, no `K1W` move: its pcs among the
nine from `.sp6 + 56` (`hpc`), `ownG` `own2b … 0` where its run ends
(`hlast`). -/
theorem blk1 (hpa : textProgram SccCertificate.asm = .ok o.prog)
    (hwp : textProgram SccCertificate.asm = .ok wakeProg) (hlo0 : Λ0.code.lo = lo) {l : WeakMem.AllocLabel}
    {b n : Nat} (hl : Spike.Lib.WakeLoadT.L0T (Ly).Λ l = none) {R : Region} {m0 : MachineData} {cP : Spike.Lib.Ctl}
    {cA mT : BitVec 64} (hpre : Pre hp i l b R cP cA mT) {nd : ND} {blk : List Directive} {lb : Label} {k : Nat}
    (hb : Scc.Cert.Rt.A64.blockAt wakeProg lb k blk = true) (he : (Ly).lab lb + Int64.ofNat (4 * k) = nd.pc)
    (hok : Spike.Lib.A64.Flow.okBlk (-80) 0 nd.o blk = true)
    (hcls : (blk.all fun d => (Spike.Lib.A64.Flow.classify d).isSome) = true)
    (hnr : Spike.Lib.A64Consumer.noRetBlk blk = true)
    (hphb : Spike.Lib.A64Consumer.blkPh (Scc.Cert.Rt.A64.okPcOf lo wakeProg (Ly).Λ) Spike.Lib.A64.WakePh.ph2b
      (fun _ => false) (Ly).lab ((Ly).lab lb + Int64.ofNat (4 * k)) 0 blk = true)
    {Es : List Nat} (hchk : Spike.Lib.A64.WakeWf.dChkAW lb k Es [] [] blk = true)
    (hE : ∀ σ c, nd.J σ c → ∀ j, j < blk.length → j ∈ Es →
      (arun (Ly).lab (blk.take (j + 1)) ⟨nd.pc, nd.o, σ⟩).σ.regs.X0 ≠ 4)
    (hac : ∀ (s : State) σ c j m, nd.J σ c → j < blk.length →
      Abs R (arun (Ly).lab (blk.take j) ⟨nd.pc, nd.o, σ⟩).so m (arun (Ly).lab (blk.take j) ⟨nd.pc, nd.o, σ⟩).σ →
      Spike.Lib.A64.ThreadsAb.Ac (Ly).lab pfxM { s with st := (m, nd.pc + Int64.ofNat (4 * j)) })
    (hkeep : Spike.Lib.WakeSrcCtl.keepsSlot (-72) nd.o blk = true ∧ Spike.Lib.WakeSrcCtl.keepsSlot (-80) nd.o blk = true)
    (hJ : ∀ σ c, nd.J σ c → c = cP ∧ MS cA mT σ)
    (d : Nat) (hd : d + blk.length ≤ 9)
    (hlb : ∀ X, codeOf lo wakeProg ".L21_wc_main.sp6" = some X → ∃ x, codeOf lo wakeProg lb = some x ∧
      x + 4 * k = X + 56 + 4 * d)
    (hlast : ∀ σ c, nd.J σ c → ∀ (s : State) m, Abs R (arun (Ly).lab blk ⟨nd.pc, nd.o, σ⟩).so m
      (arun (Ly).lab blk ⟨nd.pc, nd.o, σ⟩).σ → s.st = (m, (arun (Ly).lab blk ⟨nd.pc, nd.o, σ⟩).pc) →
        (∀ X, codeOf lo wakeProg ".L21_wc_main.sp6" = some X → ∃ q < 9, pcOf s = X + 56 + 4 * q) ∨
        (pcOf s = ((Ly).lab "scc_rt_abort").toBitVec.toNat ∧ Spike.Lib.A64.WakePh.x30At (Ly) ".L21_wc_main.sp11" s)) :
    BlkW (W1X hp i E Dt Ctx ls0 l b n) (K1W hp i E) (Ly).exe (endR hp i) R (DFrame R m0) nd blk := by
  obtain ⟨hsrc, hcA, hmT, hR, hal, hlo', hhi, -⟩ := hpre
  have hprog := Spike.Lib.WakeSrcCtl.prog_W hp i hpa hwp
  have hlo := Spike.Lib.A64.WakePh.StartPlaceLy.hlo_W hp i hlo0
  have hlab := Spike.Lib.WakeOAb.hlab_W hp i hpa hwp hlo0
  have hsite := Spike.Lib.PlaceW.site_ofPlaceW hp i
  have hΛ := Spike.Lib.PlaceW.abortLbl_of_placeW (Spike.Lib.PlaceW.link i hp)
  obtain ⟨X, hX, hF⟩ := of_atL (Bool.and_eq_true _ _ ▸ blkFacts_ok).1
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hF
  obtain ⟨⟨⟨⟨⟨hX1, -⟩, -⟩, hG⟩, hT⟩, hph9⟩ := hF
  obtain ⟨G, hG, hXG⟩ := of_atL hG
  obtain ⟨T, hT, hTX⟩ := of_atL hT
  have eX := toNat_lab hlab hX (by omega)
  have hq : ∀ j < blk.length, ∃ q < 9, (nd.pc + Int64.ofNat (4 * j)).toBitVec.toNat = X + 56 + 4 * q := by
    intro j hj
    obtain ⟨x, hx, hxk⟩ := hlb X hX
    refine ⟨d + j, by omega, ?_⟩
    rw [← he, hlab _ _ hx, ← Int64.ofNat_add, ← Int64.ofNat_add, toNat_ofNat (by omega)]; omega
  have hown : ∀ (s : State) q, q < 9 → pcOf s = X + 56 + 4 * q → ownG (Ly) aN s = own2b (Ly) aN 0 := by
    intro s q hq hs
    have hg : Spike.Lib.A64.WakePh.Good2b (Ly) s := .inr (.inl (by
      unfold Spike.Lib.A64.WakePh.inPc; rw [eX, toNat_lab hlab hG (by simp at hXG; omega), hs]
      simp at hXG; omega))
    have := hph9 q hq
    simp only [beq_iff_eq] at this
    rw [Spike.Lib.A64.WakePh.ownG_2b hlab hg, hs, Spike.Lib.A64.WakePh.ph2b_eq, this.1]
  obtain ⟨A, hA, hAF⟩ := of_atL (Bool.and_eq_true _ _ ▸ blkFacts_ok).2
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hAF
  obtain ⟨W, hW, hAW⟩ := of_atL hAF.2
  simp only [decide_eq_true_eq] at hAW
  have hab : ∀ s : State, pcOf s = ((Ly).lab "scc_rt_abort").toBitVec.toNat →
      Spike.Lib.A64.WakePh.x30At (Ly) ".L21_wc_main.sp11" s → ownG (Ly) aN s = own2b (Ly) aN 0 := by
    intro s hs hx
    have eA := toNat_lab hlab hA (by omega)
    have hg : Spike.Lib.A64.WakePh.Good2b (Ly) s := .inr (.inr ⟨by
      unfold Spike.Lib.A64.WakePh.inPc; rw [hs, toNat_lab hlab hW (by omega), eA]; omega, hx, fun ⟨h13, _⟩ =>
        Spike.Lib.WakeRefAbW.lab_ne hlab (l₁ := ".L3_scc_rt_alloc_tcb.sp13") (l₂ := ".L21_wc_main.sp11")
          (by unfold Spike.Lib.WakeRefAbW.labNe; rw [← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel)
          (congrArg BitVec.toNat (h13.symm.trans hx))⟩)
    rw [Spike.Lib.A64.WakePh.ownG_2b hlab hg, hs, Spike.Lib.A64.WakePh.ph2b_eq, eA, hAF.1.1]
  have hag := Spike.Lib.A64.WakePh.WcSp4W.agreeBlk (a := aN) (F := DFrame R m0) hsite
    (Spike.Lib.A64.Flow.code_of (Ly).lays rfl (hprog ▸ hb) he) hok hR hal (by omega) (by omega)
    (fun j hj => by
      obtain ⟨q, -, e⟩ := hq j hj
      rw [e, toNat_lab hlab hT (by simp at hTX; omega)]; simp at hTX; omega)
    (fun σ c _ j hj s m _ hs => by
      obtain ⟨q, hq9, e⟩ := hq j hj
      exact hown s q hq9 (by unfold pcOf; rw [hs]; exact e))
    (fun σ c hJc s m hA' hs => (hlast σ c hJc s m hA' hs).elim (fun h => let ⟨q, hq9, e⟩ := h X hX; hown s q hq9 e)
      fun h => hab s h.1 h.2)
  have hokc : ∀ j < blk.length, okC (nd.pc + Int64.ofNat (4 * j)).toBitVec.toNat = true := fun j hj => by
    obtain ⟨q, hq9, e⟩ := hq j hj
    have := hph9 q hq9
    simp only [beq_iff_eq] at this
    rw [e]; exact this.2
  have hst := Spike.Lib.A64.WakePh.WcSp4W.blk_c hprog hlo hsite hΛ (own2b (Ly) aN 0) (Λ := (Ly).Λ)
    (rS := ⟨0, 0⟩) hb he hok hR hal (by omega) (by omega) hcls hnr hokc hag
  obtain ⟨hlc, hlm⟩ := Spike.Lib.WakeRefSeg.lbl_of_toNat hl hcA hmT
  have hI2 := Spike.Lib.A64.WakePh.instOk2bP hprog hlo aN (rS := ⟨0, 0⟩) hsite
  have hW := Spike.Lib.A64.WakeWf.blkW_wf (ar := WakeOD.arW hp i) (p := Spike.Lib.WakeT1.wakeSrc)
    (Cl := WakeOD.ClW hp i) (Ctx := fun _ _ _ => False)
    (lsize := Spike.Lib.A64ConsumerA.updN (Spike.Lib.WakeLoadT.ls0T ls0) l n) (fs := [])
    (Spike.Lib.A64.WakePh.CalWf.blkW_dt (Dt := Dt) hst)
    (Spike.Lib.A64.WakeWf.blkW_dispAbI hI2 (hprog ▸ hb) he hok hR hal (by omega) (by omega)
      ⟨by decide, by omega, by omega⟩ hphb hnr (Spike.Lib.A64.WakeWf.dChkAW_sound hlab hchk)
      (fun _ _ _ _ _ _ _ h => by simp at h) hE (fun _ _ _ _ _ h => by simp at h))
    (fun s σ c _ _ _ _ _ _ hj j hk m hA _ => ⟨Spike.Lib.A64ConsumerA.AcSt.of_ac (hac s σ c j m hj hk hA),
      fun _ h => h⟩) (fun _ h => h.2)
    (fun s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9 => by
      have hP := Spike.Lib.WakeSrcCtl.placedSE_blkMS (Λ := (Ly).Λ) hsrc ⟨by decide, by omega, by omega⟩
        ⟨by decide, by omega, by omega⟩ hJ hkeep hlc hlm s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9
      obtain ⟨rfl, -⟩ := hJ σ c a7
      exact ⟨⟨fun _ => (Spike.Lib.WakeSrcCtl.spawnSrc_ctl hsrc).1, hP.1,
        (Spike.Lib.WakeSrcCtl.spawnSrc_ctl hsrc).2⟩, fun _ h => h⟩)
    (Spike.Lib.A64.WakeWf.blkW_noWrC (Spike.Lib.A64.AllocG.blkW_noWr hI2 (hprog ▸ hb) he hok hR hal
      (by omega) (by omega)))
    (Spike.Lib.A64.WakeWf.blkW_abortWf (fun j hj s _ _ h3 => (hI2.off s (by
      rw [Spike.Lib.A64.WakePh.okPc_eq (Λ := (Ly).Λ) hΛ]; unfold pcOf; rw [h3]; exact hokc j hj)).1))
  have e : (Ly).endPc = endR hp i := by
    show Scc.Cert.Rt.A64.endOf (Ly).exe (Ly).prog (Ly).pfx = _; rw [hprog]
  have hsT := Spike.Lib.WakeOSide.aW_site hp i hpa hwp (by rw [hprog]; exact hwp) hsite E
  intro s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9
  obtain ⟨q, hq9, hpcj⟩ := hq j hj
  have hc : pcOf { s with st := (m, nd.pc + Int64.ofNat (4 * j)) } ≠ Spike.Lib.A64.Flow.WakeWc.clonePc (Ly) := by
    show _ ≠ ((Ly).lab ".L21_wc_main.sp6" + Int64.ofNat (4 * 13)).toBitVec.toNat
    unfold pcOf; rw [hpcj, hlab _ _ hX, toNat_off _ _ (by omega)]; omega
  have ha : pcOf { s with st := (m, nd.pc + Int64.ofNat (4 * j)) } ≠ (WakeOSide.aW hp i E).toBitVec.toNat := by
    unfold pcOf; rw [hpcj, hsT, toNat_lab hlab hT (by simp at hTX; omega)]; simp at hTX; omega
  refine ⟨⟨?_, Spike.Lib.WakeH1Inv.x1W_off hc ha⟩,
    Spike.Lib.A64.Flow.WakeWc.takeCKS_none (fun _ h => h.1) (fun h => ha (by unfold pcOf; rw [h])) hc⟩
  have := (hW s σ c a1 (a2.trans e.symm) a3 a4 a5 a6 a7 j hj m a8 a9).1
  unfold WakeOPremW.W1W Spike.Lib.A64.WakeWf.W1 WakeOD.AbW WakeOD.AcW
  rw [Spike.Lib.A64.Flow.Worker.Wake.AbOffW.marks_target (Ly) hpa]
  exact this

/-- **`RefBlk`**: `blk1` at `cb` (`.sp6 + 56`), `cl` (`.clone9`) and `flB`
(`.1_spawnfail5`), their runs ending at `.clone9` (the `cbz` not taken),
`.1_spawnfail5` (the `b.lt` taken) and `scc_rt_abort` from `.sp11`'s return
address; `l` not a static label (`hl`). -/
theorem refBlk (hpa : textProgram SccCertificate.asm = .ok o.prog)
    (hwp : textProgram SccCertificate.asm = .ok wakeProg) (hlo0 : Λ0.code.lo = lo) {l : WeakMem.AllocLabel}
    {b n : Nat} (hl : Spike.Lib.WakeLoadT.L0T (Ly).Λ l = none) : RefBlk hp i E Dt Ctx ls0 l b n := by
  intro R m0 cP cA mT hpre
  have hlab := Spike.Lib.WakeOAb.hlab_W hp i hpa hwp hlo0
  have hΛ := Spike.Lib.PlaceW.abortLbl_of_placeW (Spike.Lib.PlaceW.link i hp)
  have hoff : R.Off (-32) := ⟨by decide, by have := hpre.2.2.2.2.2.1; omega, by have := hpre.2.2.2.2.2.2.1; omega⟩
  have hin := Spike.Lib.A64.Flow.Worker.Wake.SpawnFail.wake_failIn
  simp only [Spike.Lib.A64.Flow.Worker.Wake.SpawnFail.failIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨hcb, -⟩, hcl⟩, hfl⟩ := hin
  have hF : ∀ X, codeOf lo wakeProg ".L21_wc_main.sp6" = some X → X + 100 < 2 ^ 63 ∧
      codeOf lo wakeProg (pfxM ++ ".clone9") = some (X + 60) ∧
      codeOf lo wakeProg (pfxM ++ ".1_spawnfail5") = some (X + 84) := by
    intro X hX
    obtain ⟨X', hX', h⟩ := of_atL (Bool.and_eq_true _ _ ▸ blkFacts_ok).1
    obtain rfl : X' = X := Option.some.inj (hX'.symm.trans hX)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, -⟩, -⟩, -⟩ := h
    obtain ⟨y, hy, e⟩ := of_atL h2
    obtain ⟨z, hz, e'⟩ := of_atL h3
    simp only [beq_iff_eq] at e e'
    exact ⟨h1, e ▸ hy, e' ▸ hz⟩
  refine ⟨blk1 hp i E Dt Ctx ls0 hpa hwp hlo0 hl hpre hcb (by simp only [fN, Spike.Lib.A64.Flow.ofNat4_succ])
    cbP_ok (by decide) (cb_noRet _) (Spike.Lib.A64.WakePh.refPh_cb hΛ hlab) (Es := []) (by decide +kernel)
    (fun _ _ _ _ _ h => by simp at h) (fun s σ c j m hJ hj hA => ac_cb s σ c j m hJ hj hA) (Spike.Lib.WakeSrcCtl.keeps_fN _ (by simp))
    (fun σ c h => ⟨h.1, h.2.2⟩) 0 (by decide) (fun X hX => ⟨X, hX, by omega⟩) ?_,
    blk1 hp i E Dt Ctx ls0 hpa hwp hlo0 hl hpre hcl (by simp only [fN, Spike.Lib.A64.Flow.ofNat4_zero])
    cl_ok (by decide) (cl_noRet _) (Spike.Lib.A64.WakePh.refPh_cl hΛ hlab) (Es := []) (by decide +kernel)
    (fun _ _ _ _ _ h => by simp at h) (fun s σ c j m hJ hj hA => ac_cl hoff s σ c j m hJ hj hA) (Spike.Lib.WakeSrcCtl.keeps_fN _ (by simp))
    (fun σ c h => ⟨h.1, h.2.2⟩) 1 (by decide) (fun X hX => ⟨X + 60, (hF X hX).2.1, by omega⟩) ?_,
    blk1 hp i E Dt Ctx ls0 hpa hwp hlo0 hl hpre hfl (by simp only [fN, Spike.Lib.A64.Flow.ofNat4_zero])
    flB_ok (by decide) flB_noRet (Spike.Lib.A64.WakePh.refPh_fl hΛ hlab) (Es := [1]) (by decide +kernel)
    (fun σ c _ j hj h => by
      simp at h; subst h; show (arun _ Spike.Lib.A64.Flow.Worker.Wake.SpawnFail.flB _).σ.regs.X0 ≠ 4
      rw [fN, flB_run]; dsimp only; decide) (fun s _ _ j m _ hj _ => ac_fl s j m hj) (Spike.Lib.WakeSrcCtl.keeps_fN _ (by simp))
    (fun σ c h => h) 7 (by decide) (fun X hX => ⟨X + 84, (hF X hX).2.2, by omega⟩) ?_⟩
  · intro σ c hJ s m _ hs
    refine .inl fun X hX => ⟨1, by decide, ?_⟩
    have hne : σ.regs.X0.toBitVec ≠ 0#64 := hJ.2.1.ne_zero
    unfold pcOf; rw [hs]; simp only [fN, cbP_run, cbPT_run, hne, ↓reduceIte]
    show ((Ly).lab ".L21_wc_main.sp6" + Int64.ofNat (4 * 13) + 4 + 4).toBitVec.toNat = _
    rw [hlab _ _ hX, show (4 : Int64) = Int64.ofNat 4 from rfl, ← Int64.ofNat_add, ← Int64.ofNat_add,
      ← Int64.ofNat_add, toNat_ofNat (by have := (hF X hX).1; omega)]
  · intro σ c hJ s m _ hs
    refine .inl fun X hX => ⟨7, by decide, ?_⟩
    have hlt := subs0_lt hJ.2.1.slt
    unfold pcOf; rw [hs]; simp only [fN, cl_run, clT_run, hlt, ↓reduceIte, Spike.Lib.A64.Flow.rl]
    rw [toNat_lab hlab (hF X hX).2.2 (by have := (hF X hX).1; omega)]
  · intro σ c _ s m hA hs
    simp only [fN, flB_run] at hA hs
    refine .inr ⟨by unfold pcOf; rw [hs], ?_⟩
    unfold Spike.Lib.A64.WakePh.x30At
    rw [show s.st.1 = m by rw [hs], hA.regs]
    exact (ofInt_add8 _).trans (raT_sp11 hlab)

end Inst

end Spike.Lib.WakeRefStub

/-- info: 'Spike.Lib.WakeRefStub.refBlk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeRefStub.refBlk
