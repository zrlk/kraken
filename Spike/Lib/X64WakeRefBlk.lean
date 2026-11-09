/-
**`RefBlk`: the refusal path's test and three blocks inside `W1X`** (x86-64,
wake.w; the twin of `Spike/Lib/A64WakeRefBlk.lean`): the `testq` row `ts`
at `.x21 + 48`, the `je` block at `.x21 + 51`, `.x22`'s block and
`.spawnfail5`'s, inside `W1W` and `X1W`, under no `K1W` move. Each node:

- `SFactsSt2` at `ownG` (`WcSp4W.blk_c`/`node_c` at the constant instance
  `own2b … 0`, where `ownG` agrees with it, `WcSp4W.agreeBlk`), lifted to
  `ownGXW` (`blkW_cstOkB`/`nodeL2` at `Lft2`: both TCB words held, `InC`,
  `%rsp` on the pool by `band_pre`);
- the write abort's phase kept (`AllocG.blkW_ab`/`nodeW_ab_fi`, the
  targets off `abPcs` decided at the code labels, `refAbOk`;
  `.spawnfail5`'s call enters the dispatcher at `%rdi = 5`,
  `AllocG.not_ab_abort`);
- in the threads abort phase `Ac` (`SpawnFail.ac_ts`/`ac_je'`/`ac_x22`/
  `ac_fl`), placed (`placedSE_blkMS`/`placedSE_nodeMS`), writing nothing to
  the arena or the counter, off the abort sites;
- off the clone's `syscall` and the take site (`X1W`, `takeCKS_none`).

- `cl`, `clOk`, `codeLabel_cl`, `lab_cl`, `lab_clN`: a code label's
  resolved address in wake's code; `refRange`: the decided facts at them.
- `refPc`, `refPc_spec`: a refusal pc, decided: in `[.x21 + 47, .stk)`,
  off the sites, at `ph2b` `0`.
- `own_ref`, `cls_ref`: `ownG` is `own2b … 0` and both TCB words are held
  at a refusal pc (on the pool).
- `band_pre`: `Pre`'s region `[-72, 8]` on the pool (`BandOnP`), from its
  base `64` below stack 0's top and A8's `stacks_sub`.
- `refAbOk`, `refAbOk_ok`: the targets' check at the code labels.
- `keep_test`: the `testq` keeps `%rsp`, `%rbp`.
- `blk1`: one block; `ts1`: the row; `fl_last`: `.spawnfail5`'s run's end;
  `refBlk`: the piece.

**Where this differs from AArch64**: a row `ts` (a `NodeW`, the `testq`)
and three blocks `je`, `x22`, `fl` (A64's three blocks `cb`, `cl`, `fl`);
`W1W` owns `ownGXW`, so each node's `SFactsSt2` at `ownG` is lifted by
`Lft2` (`blkW_cstOkB`/`nodeL2` with `cls_poolW`), whose band on the pool
`band_pre` derives from `Pre` (no A64 counterpart); `refBlk` carries A13's
data part `hA13` (the TCB words off the counters, `tcbM_ne_ntA_W`,
`tcb2_notG_W`) besides A64's premises; the write abort's phase is
`AllocG.blkW_ab` with a decided target check (A64's `blkW_dispAbI`), the
exit call's target the dispatcher at `%rdi = 5` (`not_ab_abort`, A64's
`hE`); `.spawnfail5`'s run ends at `scc_rt_abort` with `.Lwc_main.x5`
pushed at `-72` (`raAt`, a private word; A64's `x30At`); the pcs are
decided at the code labels (`cl`: `.x21`, `.stk`, `scc_rt_abort`, the
take site, the clone's `syscall` at `.x21 + 46`, `refRange`); the assembly
is a parameter `asm`.
-/
import Spike.Lib.X64WakeRefMap
import Spike.Lib.X64WakeRefPh
import Spike.Lib.X64SpawnFailAC
import Spike.Lib.X64WakeWcSp4W
import Spike.Lib.X64WakeWfCal
import Spike.Lib.X64WakeOwnLft2
import Spike.Lib.X64WakeOwnSW
import Spike.Lib.X64WakeOwnT2W
import Spike.Lib.X64WakeOwnGAb
import Spike.Lib.X64WakeOwnPark
import Spike.Lib.X64AllocGAb
import Spike.Lib.X64WakeWcl
import Spike.Lib.X64WakeSrcCtl
import Spike.Lib.X64WakeWcK1

namespace Spike.Lib.X64.WakeRefStub

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib (Region PlaceWX FragS)
open Spike.Lib.X64 (ND At BlkW NodeW DFrame Abs arun cellOff okBlk)
open Spike.Lib.X64.Rt (RuntimeLayout InstOk)
open Spike.Lib.X64ConsumerA (SFactsSt2 StSucc SpAt AbSt AcSt rsp_of_abs)
open Spike.Lib.X64Consumer (Lsize)
open Spike.Lib.X64.WakePh (lo ownG own2b ownGXW okC ph2bC Cst tM tW BandOnP Good2b inPc raAt raAddr raSp abFns
  selfOwn selfOwnW spPool Keep)
open Spike.Lib.X64.WakePh.SpawnFail (fN flB flL MS)
open Spike.Lib.X64.WakePh.Parent (tsB jeB x22B x22L)
open Spike.Lib.X64.WakePh.WcClone (oW x21L)
open Spike.Lib.X64.WakePh.StartWf (pfxM)
open Spike.Lib.X64.WakeH1Inv (K1W endR)
open Spike.Lib.X64.WakeBoxW (W1X)
open Spike.Lib.X64.ThreadsAb (raT)
open Spike.Lib.X64WakeT1 (wakeSrc)
open Spike.Lib.X64WakeLoadT (L0T)
open Spike.Lib.X64.Rt.Reserve (ntA)
open Scc.Cert.Rt.X64 (blockAtB codeT codeT_eq code_field)
open SccCode (wakeCells)
open Kraken.Promising.Lower.X64 (CellAt)
open Scc.Sem.X64 (privLoad)

/-! ## The refusal pcs -/

/-- **A code label's resolved address** in wake's code (`0` off it). -/
def cl (l : Label) : Nat := (codeT lo wakeCells l).getD 0

/-- `l` is a code label of wake's, below `2 ^ 63`. -/
def clOk (l : Label) : Bool := (codeT lo wakeCells l).isSome && decide (cl l < 2 ^ 63)

theorem codeLabel_cl {l : Label} (h : clOk l = true) : codeLabel lo wakeCells l = some (cl l) := by
  rw [← codeT_eq]
  unfold clOk at h
  unfold cl
  cases hc : codeT lo wakeCells l with
  | none => simp [hc] at h
  | some x => rfl

/-- **The refusal path's facts at the code labels**: the labels laid out,
`[.x21 + 47, .stk)` inside `InC` and past `scc_rt_abort`'s range `InAb`
(ending at `scc_rt_thr_worker`) and the take site, `.Lscc_rt_start.x1`
below `scc_rt_abort`, `scc_rt_abort` at `ph2b` `0`. -/
theorem refRange :
    clOk x21L = true ∧ clOk ".Lwc_main.stk" = true ∧ clOk Spike.Lib.X64.Flow.Ret0.StackTake.siteL = true ∧
      clOk "scc_rt_abort" = true ∧ clOk "scc_rt_thr_worker" = true ∧ clOk ".Lscc_rt_start.x1" = true ∧
      Spike.Lib.X64.WakePh.InC (cl x21L + 47) ∧ Spike.Lib.X64.WakePh.InC (cl ".Lwc_main.stk" - 1) ∧
      cl "scc_rt_thr_worker" ≤ cl x21L + 47 ∧ ¬ Spike.Lib.X64.WakePh.InAb (cl "scc_rt_thr_worker") ∧
      Spike.Lib.X64.WakePh.InAb (cl "scc_rt_thr_worker" - 1) ∧
      cl Spike.Lib.X64.Flow.Ret0.StackTake.siteL < cl x21L + 46 ∧ cl ".Lscc_rt_start.x1" ≤ cl "scc_rt_abort" ∧
      cl "scc_rt_abort" < cl "scc_rt_thr_worker" ∧ ph2bC (cl "scc_rt_abort") = 0 := by
  decide +kernel

/-- **A refusal pc**: past the clone's `syscall` and before `.stk`
(`[.x21 + 47, .stk)`, inside `InC`), off the sites, at `ph2b` `0`. -/
def refPc (q : Nat) : Bool := decide (cl x21L + 47 ≤ q ∧ q < cl ".Lwc_main.stk") && okC q && ph2bC q == 0

theorem refPc_spec {q : Nat} (h : refPc q = true) :
    cl x21L + 47 ≤ q ∧ q < cl ".Lwc_main.stk" ∧ okC q = true ∧ ph2bC q = 0 := by
  unfold refPc at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

section L

variable {L : RuntimeLayout} {a : BitVec 64}
  (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
include hlab

/-- **A code label's address** in the layout is `cl`'s. -/
theorem lab_cl {l : Label} (h : clOk l = true) : L.lab l = Int64.ofNat (cl l) := hlab _ _ (codeLabel_cl h)

theorem lab_clN {l : Label} (h : clOk l = true) : (L.lab l).toBitVec.toNat = cl l := by
  have hb : cl l < 2 ^ 63 := by
    unfold clOk at h; simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h.2
  rw [lab_cl hlab h]
  show (BitVec.ofNat 64 (cl l)).toNat = cl l
  rw [BitVec.toNat_ofNat]; omega

/-- **`ownG` at a refusal pc** is `own2b L a 0`. -/
theorem own_ref {s : State} (h : refPc (pcOf s) = true) : ownG L a s = own2b L a 0 := by
  obtain ⟨h1, h2, -, h4⟩ := refPc_spec h
  obtain ⟨o21, oStk, -⟩ := refRange
  have hg : Good2b L s := .inr (.inl (by unfold inPc; rw [lab_clN hlab o21, lab_clN hlab oStk]; omega))
  rw [Spike.Lib.X64.WakePh.ownG_2b hlab hg, Spike.Lib.X64.WakePh.ph2b_eq, h4]

/-- **Both TCB words at a refusal pc** with `%rsp` in a band on the pool. -/
theorem cls_ref {R : Region} {slo shi : Int} (hb : BandOnP L R slo shi) :
    ∀ s : State, refPc (pcOf s) = true → SpAt R slo shi s → Cst L (tM L) (tW L) s := fun s h hsp => by
  obtain ⟨h1, h2, -, -⟩ := refPc_spec h
  obtain ⟨-, -, -, -, -, -, c1, c2, c3, c4, c5, -⟩ := refRange
  refine Spike.Lib.X64.WakePh.cls_poolW hlab hb s ⟨.inr ?_, ?_⟩ hsp
  · unfold Spike.Lib.X64.WakePh.InC at *; omega
  · unfold Spike.Lib.X64.WakePh.InAb at *; omega

end L

/-- **`Pre`'s frame band on the pool**: `[-72, 8]` of `R` in stack 0 (its
base `64` below stack 0's top, A8's `stacks_sub`). -/
theorem band_pre {L : RuntimeLayout} {R : Region} (hR : R.OK) (hlo : R.lo ≤ -320) (hhi : 16 ≤ R.hi)
    (hbase : R.base.toNat + 64 = L.stacksA.toNat + 16384) : BandOnP L R (-72) 8 := by
  intro k h1 h2
  obtain ⟨hs1, hs2⟩ := L.stacks_sub
  simp only at hs1 hs2
  have e := Region.addr_toNat_of hR (k := k) (by omega) (by omega)
  omega

/-! ## The targets off the write abort's pcs -/

/-- The labels the targets' check reads. -/
def refAbLabs : List String :=
  Spike.Lib.X64.AllocG.abLabs ++ Spike.Lib.LowerX64.blkLabs jeB ++ Spike.Lib.LowerX64.blkLabs x22B ++
    [x21L, x22L, flL]

theorem refAbLabs_ok : refAbLabs.all (fun x => (codeLabel lo wakeCells x).isSome) = true := by decide +kernel

/-- **The refusal path's targets off the write abort's pcs** at the code
labels: the `je`'s and `.x22`'s blocks', the `testq`'s and `movq $5,
%rdi`'s next pcs, the exit call's target off every pc of `Ab` but the
dispatcher's prologue. -/
def refAbOk : Bool :=
  let lab := Spike.Lib.LowerX64.labC lo wakeCells
  Spike.Lib.X64.AllocG.blkAbC lab (lab x21L + Int64.ofNat 51) 0 jeB &&
  Spike.Lib.X64.AllocG.blkAbC lab (lab x22L + Int64.ofNat 0) 0 x22B &&
  !(Spike.Lib.X64.WriteAb.abPcs lab).contains (lab x21L + Int64.ofNat 48 + Int64.ofNat 3) &&
  !(Spike.Lib.X64.WriteAb.abPcs lab).contains (lab flL + Int64.ofNat 0 + Int64.ofNat 7) &&
  !(Spike.Lib.X64.AllocG.abNoDispE lab).contains (lab "scc_rt_abort")

theorem refAbOk_ok : refAbOk = true := by decide +kernel

/-- **`refAbOk` at any labels agreeing with the code labels.** -/
theorem refAbOk_spec {lab : Label → Int64} (hlab : ∀ l x, codeLabel lo wakeCells l = some x → lab l = Int64.ofNat x) :
    Spike.Lib.X64ConsumerA.blkAb lab (lab x21L + Int64.ofNat 51) 0 jeB = true ∧
    Spike.Lib.X64ConsumerA.blkAb lab (lab x22L + Int64.ofNat 0) 0 x22B = true ∧
    lab x21L + Int64.ofNat 48 + Int64.ofNat 3 ∉ Spike.Lib.X64.WriteAb.abPcs lab ∧
    lab flL + Int64.ofNat 0 + Int64.ofNat 7 ∉ Spike.Lib.X64.WriteAb.abPcs lab ∧
    lab "scc_rt_abort" ∉ Spike.Lib.X64.AllocG.abNoDispE lab := by
  have hL := Spike.Lib.X64.WakeWf.lab_labC hlab refAbLabs_ok
  have ha : ∀ l ∈ Spike.Lib.X64.AllocG.abLabs, lab l = Spike.Lib.LowerX64.labC lo wakeCells l :=
    fun l h => hL l (by simp only [refAbLabs, List.mem_append]; exact .inl (.inl (.inl h)))
  have hj : ∀ l ∈ Spike.Lib.LowerX64.blkLabs jeB, lab l = Spike.Lib.LowerX64.labC lo wakeCells l :=
    fun l h => hL l (by simp only [refAbLabs, List.mem_append]; exact .inl (.inl (.inr h)))
  have hx : ∀ l ∈ Spike.Lib.LowerX64.blkLabs x22B, lab l = Spike.Lib.LowerX64.labC lo wakeCells l :=
    fun l h => hL l (by simp only [refAbLabs, List.mem_append]; exact .inl (.inr h))
  have e21 := hL x21L (by simp [refAbLabs])
  have e22 := hL x22L (by simp [refAbLabs])
  have efl := hL flL (by simp [refAbLabs])
  have eab := ha "scc_rt_abort" (by simp [Spike.Lib.X64.AllocG.abLabs])
  have h := refAbOk_ok
  simp only [refAbOk, Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← Spike.Lib.X64.AllocG.blkAbC_eq, Spike.Lib.X64.AllocG.blkAbC_congr hj ha, e21]; exact h1
  · rw [← Spike.Lib.X64.AllocG.blkAbC_eq, Spike.Lib.X64.AllocG.blkAbC_congr hx ha, e22]; exact h2
  · rw [Spike.Lib.X64.AllocG.abPcs_congr ha, e21]; exact h3
  · rw [Spike.Lib.X64.AllocG.abPcs_congr ha, efl]; exact h4
  · rw [Spike.Lib.X64.AllocG.abNoDispE_congr ha, eab]; exact h5

/-! ## The `testq` keeps the frame registers -/

/-- **`testq %rax, %rax`** keeps `%rsp` and `%rbp`. -/
theorem keep_test {μ : Marks} {s s' : State} {z : Nat}
    (hc : CellAt s (Spike.Lib.X64.FI.toDir (.test_rr .rax .rax)) z) (h : StSucc μ s s') : Keep s s' := by
  have hs : abi.atSys s = false :=
    Scc.Sem.X64.atSyscall_false_of_cellAt hc (by intro w w' h; cases h)
  rcases h with ⟨-, tree, htr, hl⟩ | ⟨hs', -⟩ | ⟨-, -, -, m, rfl⟩
  · obtain ⟨t, ht, hsil⟩ := Spike.Lib.X64.exec_fi hc
    rw [ht] at htr
    cases htr
    obtain ⟨fl, rfl⟩ := Spike.Lib.X64.WakePh.Tcb2W.silent_leaf hsil hl
    exact ⟨rfl, rfl, (Scc.Sem.X64.nextPc_of_cellAt hc).symm⟩
  · rw [hs] at hs'; cases hs'
  · exact Spike.Lib.X64.WakePh.keep_take m

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (asm : Asm) (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (Dt : State → Prop) (Ctx : FragS isa) (ls0 : Lsize)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

set_option hygiene false in
/-- The layout's labels. -/
local notation "lbW" => (_root_.Executable.labels (RuntimeLayout.ofPlaceWX hp i).exe).label

set_option hygiene false in
/-- The owned words' counter address. -/
local notation "aN" => ntA (RuntimeLayout.ofPlaceWX hp i).lab

/-- **The clone's `syscall`** is at `.x21 + 46`. -/
theorem clone_eq (hlab : ∀ l x, codeLabel lo wakeCells l = some x → (Ly).lab l = Int64.ofNat x) :
    Spike.Lib.X64.Flow.WakeWc.clonePc (Ly) = cl x21L + 46 := by
  unfold Spike.Lib.X64.Flow.WakeWc.clonePc Spike.Lib.X64WakePreA.cloneAt
  show ((Ly).lab x21L + 46).toBitVec.toNat = _
  rw [lab_cl hlab refRange.1]
  decide +kernel

/-- **`X1W` and no `K1W` move at a refusal pc.** -/
theorem x1k1_ref (hpa : cellsOf asm = some o.prog)
    (hlab : ∀ l x, codeLabel lo wakeCells l = some x → (Ly).lab l = Int64.ofNat x)
    {l : WeakMem.AllocLabel} {b n : Nat} {s : State} {c : Spike.Lib.Ctl} (h : refPc (pcOf s) = true) :
    Spike.Lib.X64.WakeH1Inv.X1W (Ly) (Spike.Lib.X64WakeOSide.aW hp i E) (endR hp i) l
        (Spike.Lib.X64ConsumerA.upd (L0T (Ly).Λ) l b)
        (Spike.Lib.X64ConsumerA.updN (Spike.Lib.X64WakeLoadT.ls0T ls0) l n) s c [] ∧
      ∀ s', ¬ K1W hp i E s s' := by
  obtain ⟨h1, h2, -, -⟩ := refPc_spec h
  have hc : pcOf s ≠ Spike.Lib.X64.Flow.WakeWc.clonePc (Ly) := by rw [clone_eq hp i hlab]; omega
  have ha : s.st.2 ≠ Spike.Lib.X64WakeOSide.aW hp i E := fun he => by
    have := congrArg (fun x : Int64 => x.toBitVec.toNat) he
    simp only [Spike.Lib.X64WakeOSide.aW_site hp i hpa E, lab_clN hlab refRange.2.2.1] at this
    have := refRange.2.2.2.2.2.2.2.2.2.2.2.1
    unfold pcOf at h1
    omega
  exact ⟨Spike.Lib.X64.WakeH1Inv.x1W_off hc (Spike.Lib.X64.Flow.WakeWc.pcOf_ne ha),
    Spike.Lib.X64.Flow.WakeWc.takeCKS_none (fun _ h => h.1) ha hc⟩

set_option maxHeartbeats 1600000 in
/-- **One refusal block inside `W1X`**, no `K1W` move: its pcs refusal pcs
(`hq`), its prefixes' `%rsp` offsets in `[-72, 8]` (`hso`), the write
abort's phase kept (`hab`), its states in `Ac` (`hac`), main's slots kept
(`hkeep`), `ownG` `own2b … 0` and both TCB words where its run ends
(`hlast`). -/
theorem blk1 (hpa : cellsOf asm = some o.prog) (hwp : cellsOf asm = some wakeCells) (hlo0 : Λ0.code.lo = lo)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true) {l : WeakMem.AllocLabel} {b n : Nat}
    (hl : L0T (Ly).Λ l = none) {R : Region} {m0 : MachineData} {cP : Spike.Lib.Ctl} {cA mT : BitVec 64}
    (hpre : Pre hp i l b R cP cA mT) {nd : ND} {blk : List (Directive × Nat)} {lb : Label} {k : Nat}
    (hb : blockAtB wakeCells lb k blk = true) (he : lbW lb + Int64.ofNat k = nd.pc)
    (hok : okBlk (-72) 16 nd.o blk = true)
    (hcl : (blk.all fun dz => (Spike.Lib.X64.classify dz.1).isSome) = true)
    (hnr : Spike.Lib.X64Consumer.noRetBlk blk = true)
    (hq : ∀ j < blk.length, refPc (nd.pc + Int64.ofNat (cellOff blk j)).toBitVec.toNat = true)
    (hso : ∀ j ≤ blk.length, -72 ≤ (Spike.Lib.X64.WakePh.Tcb2W.soRun (blk.take j) nd.o).sp ∧
      (Spike.Lib.X64.WakePh.Tcb2W.soRun (blk.take j) nd.o).sp ≤ 8)
    (hab : BlkW (fun s _ => AbSt (Spike.Lib.X64.PhRec.μ (Ly)) (Spike.Lib.X64.WriteAb.Ab (Ly).lab) s)
      (fun _ _ => False) (Ly).exe (Ly).endPc R (DFrame R m0) nd blk)
    (hac : ∀ (s : State) σ c j m, nd.J σ c → j < blk.length →
      Abs R (arun lbW (blk.take j) ⟨nd.pc, nd.o, σ⟩).so m (arun lbW (blk.take j) ⟨nd.pc, nd.o, σ⟩).σ →
      Spike.Lib.X64.ThreadsAb.Ac (Ly).lab pfxM { s with st := (m, nd.pc + Int64.ofNat (cellOff blk j)) })
    (hkeep : Spike.Lib.X64.WakeSrcCtl.keepsSlot (-16) nd.o blk = true ∧
      Spike.Lib.X64.WakeSrcCtl.keepsSlot (-8) nd.o blk = true)
    (hJ : ∀ σ c, nd.J σ c → c = cP ∧ MS cA mT σ)
    (hlast : ∀ σ c, nd.J σ c → ∀ (s : State) m, Abs R (arun lbW blk ⟨nd.pc, nd.o, σ⟩).so m
      (arun lbW blk ⟨nd.pc, nd.o, σ⟩).σ → s.st = (m, (arun lbW blk ⟨nd.pc, nd.o, σ⟩).pc) →
      SpAt R (-72) 8 s → ownG (Ly) aN s = own2b (Ly) aN 0 ∧ Cst (Ly) (tM (Ly)) (tW (Ly)) s) :
    BlkW (fun s c => W1X asm hp i E Dt Ctx ls0 l b n s c []) (K1W hp i E) (Ly).exe (endR hp i) R (DFrame R m0)
      nd blk := by
  rw [← endR_eq hp i hpa hwp]
  obtain ⟨hsrc, hcA, hmT, hR, hlo', hhi, hbase⟩ := hpre
  have hprog := Spike.Lib.X64.WakeSrcCtl.prog_W hp i hpa hwp
  have hpL : cellsOf asm = some (Ly).prog := by rw [hprog]; exact hwp
  have hlo := Spike.Lib.X64.WakePh.StartPlaceLy.hlo_W hp i hlo0
  have hlab := Spike.Lib.X64WakeOAb.hlab_W hp i hpa hwp hlo0
  have hsite := PlaceWX.site_ofPlaceWX hp i
  have hΛ : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName := PlaceWX.abortLbl_of_placeWX (PlaceWX.link i hp)
  have hband := band_pre (L := Ly) hR hlo' hhi hbase
  have hbP : blockAtB (Ly).prog lb k blk = true := by rw [hprog]; exact hb
  have hcode : ∀ s : State, s.exe = (Ly).exe → s.endPc = (Ly).endPc → Spike.Lib.X64.CodeAt s nd.pc blk :=
    code_field (Ly).lays rfl hbP he
  -- the take site's address as `WcSp4W` states it
  have hsN := lab_clN hlab refRange.2.2.1 (L := Ly)
  rw [Spike.Lib.X64.WakePh.WcSp4W.lab_site hlab, Spike.Lib.X64.WakePh.WcSp4W.site_toNat] at hsN
  have hns : ∀ j < blk.length, (nd.pc + Int64.ofNat (cellOff blk j)).toBitVec.toNat ≠
      cl Spike.Lib.X64.Flow.Ret0.StackTake.siteL := fun j hj => by
    have := refPc_spec (hq j hj); have := refRange.2.2.2.2.2.2.2.2.2.2.2.1; omega
  have hns' : ∀ x, (Spike.Lib.X64.PhRec.μ (Ly)).site .take = some x → ∀ j < blk.length,
      (nd.pc + Int64.ofNat (cellOff blk j)).toBitVec.toNat ≠ x := fun x hx j hj => by
    rw [hsite, lab_clN hlab refRange.2.2.1] at hx
    cases hx; exact hns j hj
  have hspE : ∀ σ c, nd.J σ c → ∀ (s : State) m, Abs R (arun lbW blk ⟨nd.pc, nd.o, σ⟩).so m
      (arun lbW blk ⟨nd.pc, nd.o, σ⟩).σ → s.st = (m, (arun lbW blk ⟨nd.pc, nd.o, σ⟩).pc) → SpAt R (-72) 8 s := by
    intro σ c _ s m hA hs
    have ho := hso blk.length (Nat.le_refl _)
    rw [List.take_length, ← Spike.Lib.X64.WakePh.Tcb2W.arun_so lbW _ ⟨nd.pc, nd.o, σ⟩] at ho
    exact ⟨_, ho.1, ho.2, by rw [hs]; exact rsp_of_abs hA⟩
  have hag := Spike.Lib.X64.WakePh.WcSp4W.agreeBlk (a := aN) (F := DFrame R m0) hlab hsite hcode hok hR
    (by omega) (by omega) (fun j hj => by rw [hsN]; exact hns j hj)
    (fun σ c _ j hj s m _ hs => own_ref hlab (by unfold pcOf; rw [hs]; exact hq j hj))
    (fun σ c hJc s m hA hs => (hlast σ c hJc s m hA hs (hspE σ c hJc s m hA hs)).1)
  have hokc : ∀ j < blk.length, okC (nd.pc + Int64.ofNat (cellOff blk j)).toBitVec.toNat = true :=
    fun j hj => (refPc_spec (hq j hj)).2.2.1
  have hst0 := Spike.Lib.X64.WakePh.WcSp4W.blk_c hprog hlo hΛ hsite (own2b (Ly) aN 0) (Λ := (Ly).Λ)
    (rS := ⟨0, 0⟩) hbP he hok hR (by omega) (by omega) hcl hnr hokc hag
  have hstD := Spike.Lib.X64.WakePh.CalWf.blkW_dt (Dt := Dt) hst0
  have hL := Spike.Lib.X64.WakePh.BlkW.lft2 (Λ := (Ly).Λ) (Dt := Dt) (F := DFrame R m0)
    (Spike.Lib.X64.WakePh.blkW_cstOkB (P := fun q => refPc q = true) (Spike.Lib.X64.WakePh.tcbSep_W hp i)
      (Spike.Lib.X64.WakePh.tcbM_ne_ntA_W hp i hA13) (Spike.Lib.X64.WakePh.tcb2_notG_W hp i hA13) hcode hok hR
      (by omega) (by omega) hns' (cls_ref hlab hband) hq hso
      (fun σ c hJc s m hA _ _ hs => (hlast σ c hJc s m hA hs (hspE σ c hJc s m hA hs)).2))
  have hst : BlkW (fun s _ => SFactsSt2 (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) (ownGXW (Ly) aN) s Dt)
      (Spike.Lib.X64.PhRec.K (Ly) ⟨0, 0⟩) (Ly).exe (Ly).endPc R (DFrame R m0) nd blk :=
    fun s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9 =>
      ⟨(hL s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9).1 (hstD s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9).1,
        (hstD s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9).2⟩
  have hI := Spike.Lib.X64.WakePh.instOkW hprog hlo aN (fun _ => False) hsite (rS := ⟨0, 0⟩)
  obtain ⟨hlc, hlm⟩ := Spike.Lib.X64.WakeRefSeg.lbl_of_toNat hl hcA hmT
  have hW := Spike.Lib.X64.WakeWf.blkW_wf (ar := Spike.Lib.X64.WakeOD.arW hp i) (p := wakeSrc)
    (Cl := Spike.Lib.X64.WakeOD.ClW hp i) (Ctx := fun _ _ _ => False)
    (lbl := Spike.Lib.X64ConsumerA.upd (L0T (Ly).Λ) l b)
    (lsize := Spike.Lib.X64ConsumerA.updN (Spike.Lib.X64WakeLoadT.ls0T ls0) l n) (fs := []) hst hab
    (fun s σ c _ _ _ _ _ _ hj j hk m hA _ => ⟨Spike.Lib.X64ConsumerA.AcSt.of_ac (hac s σ c j m hj hk hA),
      fun _ h => h⟩) (fun _ h => h.2)
    (fun s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9 => by
      have hP := Spike.Lib.X64.WakeSrcCtl.placedSE_blkMS (Λ := (Ly).Λ) hsrc ⟨by decide, by omega, by omega⟩
        ⟨by decide, by omega, by omega⟩ hJ hkeep hlc hlm s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9
      obtain ⟨rfl, -⟩ := hJ σ c a7
      exact ⟨⟨fun _ => (Spike.Lib.X64.WakeSrcCtl.spawnSrc_ctl hsrc).1, hP.1,
        (Spike.Lib.X64.WakeSrcCtl.spawnSrc_ctl hsrc).2⟩, fun _ h => h⟩)
    (Spike.Lib.X64.WakeWf.blkW_noWrC (Spike.Lib.X64.AllocG.blkW_noWr hI hbP he hok hR (by omega) (by omega)))
    (Spike.Lib.X64.WakeWf.blkW_abortWf (fun j hj s _ _ h3 => (hI.off s (by
      rw [Spike.Lib.X64.WakePh.okPc_eq hΛ]; unfold pcOf; rw [h3]; exact hokc j hj)).1))
  intro s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9
  obtain ⟨hX, hK⟩ := x1k1_ref asm hp i E ls0 hpa hlab (l := l) (b := b) (n := n)
    (s := { s with st := (m, nd.pc + Int64.ofNat (cellOff blk j)) }) (c := c) (hq j hj)
  refine ⟨⟨?_, hX⟩, hK⟩
  have := (hW s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9).1
  show Spike.Lib.X64.WakeWf.Wf _ _ _ _ _ _ _ _ _ _ _ _ _ c []
  rw [Spike.Lib.X64.Flow.Worker.Wake.AbOffW.marks_target (Ly) hpL]
  exact this

set_option maxHeartbeats 1600000 in
/-- **The refusal path's `testq` row inside `W1X`**, no `K1W` move. -/
theorem ts1 (hpa : cellsOf asm = some o.prog) (hwp : cellsOf asm = some wakeCells) (hlo0 : Λ0.code.lo = lo)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true) {l : WeakMem.AllocLabel} {b n : Nat}
    (hl : L0T (Ly).Λ l = none) {R : Region} {m0 : MachineData} {cP : Spike.Lib.Ctl} {cA mT : BitVec 64}
    (hpre : Pre hp i l b R cP cA mT) :
    NodeW (fun s c => W1X asm hp i E Dt Ctx ls0 l b n s c []) (K1W hp i E) (Ly).exe (endR hp i) R (DFrame R m0)
      (fN lbW cP cA mT .ts) := by
  rw [← endR_eq hp i hpa hwp]
  obtain ⟨hsrc, hcA, hmT, hR, hlo', hhi, hbase⟩ := hpre
  have hprog := Spike.Lib.X64.WakeSrcCtl.prog_W hp i hpa hwp
  have hpL : cellsOf asm = some (Ly).prog := by rw [hprog]; exact hwp
  have hlo := Spike.Lib.X64.WakePh.StartPlaceLy.hlo_W hp i hlo0
  have hlab := Spike.Lib.X64WakeOAb.hlab_W hp i hpa hwp hlo0
  have hsite := PlaceWX.site_ofPlaceWX hp i
  have hΛ : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName := PlaceWX.abortLbl_of_placeWX (PlaceWX.link i hp)
  have hband := band_pre (L := Ly) hR hlo' hhi hbase
  have e21 := Spike.Lib.X64.WakePh.WcSp4W.lab_x21 hlab
  have hin := Spike.Lib.X64.WakePh.SpawnFail.wake_failInB
  simp only [Spike.Lib.X64.WakePh.SpawnFail.failInB, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨hts, -⟩, -⟩, -⟩ := hin
  have hbW : blockAtB wakeCells x21L 48 [(Spike.Lib.X64.FI.toDir (.test_rr .rax .rax), 3)] = true := hts
  have hbP : blockAtB (Ly).prog x21L 48 [(Spike.Lib.X64.FI.toDir (.test_rr .rax .rax), 3)] = true := by
    rw [hprog]; exact hbW
  have hpcE : (fN lbW cP cA mT .ts).pc = lbW x21L + Int64.ofNat 48 := rfl
  have hpc0 : refPc (fN lbW cP cA mT .ts).pc.toBitVec.toNat = true := by rw [hpcE, e21]; decide +kernel
  have hpc3 : refPc ((fN lbW cP cA mT .ts).pc + Int64.ofNat 3).toBitVec.toNat = true := by
    rw [hpcE, e21]; decide +kernel
  have hokc : okC (lbW x21L + Int64.ofNat 48).toBitVec.toNat = true := by rw [e21]; decide +kernel
  have hokcN : okC (fN lbW cP cA mT .ts).pc.toBitVec.toNat = true := (refPc_spec hpc0).2.2.1
  have hC : ∀ s c, At (Ly).exe (Ly).endPc R (DFrame R m0) (fN lbW cP cA mT .ts) s c →
      CellAt s (Spike.Lib.X64.FI.toDir (.test_rr .rax .rax)) 3 := fun s c hAt => by
    obtain ⟨he, hn, -, hp', -⟩ := hAt
    exact (code_field (Ly).lays rfl hbP rfl s he hn).cell0 rfl rfl hp'
  -- the state's facts at `ownG`, then at `ownGXW`
  have hI0 := InstOk.const (Spike.Lib.X64.WakePh.instOkW hprog hlo aN (fun _ => False) hsite (rS := ⟨0, 0⟩))
    (own2b (Ly) aN 0) False
  have hst0 := Spike.Lib.X64.WakePh.WcSp4W.node_c hlab hsite (o := own2b (Ly) aN 0) (z := 3)
    (n := fN lbW cP cA mT .ts)
    (Spike.Lib.X64.Rt.nodeW_fi_pre hI0 (Λ := (Ly).Λ) (rS := ⟨0, 0⟩) (lbl := fun _ => none) (F := DFrame R m0)
      hbP rfl rfl Spike.Lib.X64.WakePh.WcW.c0N_cfacts
      (by rw [Spike.Lib.X64.WakePh.okPc_eq hΛ]; exact hokc) (fun _ _ h => h) rfl)
    (by
      have hsN := lab_clN hlab refRange.2.2.1 (L := Ly)
      rw [Spike.Lib.X64.WakePh.WcSp4W.lab_site hlab, Spike.Lib.X64.WakePh.WcSp4W.site_toNat] at hsN
      have := refPc_spec hpc0; have := refRange.2.2.2.2.2.2.2.2.2.2.2.1; omega)
    (fun s hs => own_ref hlab (by unfold pcOf; rw [hs]; exact hpc0))
    (fun s hs => own_ref hlab (by unfold pcOf; rw [hs]; exact hpc3))
    (fun s c hAt => by
      have hc := hC s c hAt
      obtain ⟨tr, hex, hsl⟩ := Spike.Lib.X64.exec_fi hc
      refine ⟨_, _, hc, fun w w' h => (by cases h), hex, fun s' hu => ?_⟩
      obtain ⟨_, rfl⟩ := Spike.Lib.X64.WakePh.Tcb2W.silent_leaf hsl hu; rfl)
  have hstD := Spike.Lib.X64.WakePh.CalWf.nodeW_dt (Dt := Dt) hst0
  have hL := Spike.Lib.X64.WakePh.nodeL2 (Λ := (Ly).Λ) (Dt := Dt) hlab (Spike.Lib.X64.WakePh.tcbSep_W hp i)
    (Spike.Lib.X64.WakePh.tcbM_ne_ntA_W hp i hA13) (Spike.Lib.X64.WakePh.tcb2_notG_W hp i hA13) (sz := 3)
    (P := fun q => refPc q = true) (cls_ref hlab hband)
    (fun s c hAt s' hs => by
      have hc := hC s c hAt
      have hK : Keep s s' := keep_test hc hs
      exact ⟨hK, by rw [Spike.Lib.X64.WakePh.keep_pc hc hK, hAt.2.2.2.1]⟩)
    ⟨hpc0, hpc3⟩ ⟨by show (-72 : Int) ≤ oW.sp; decide, by show oW.sp ≤ (8 : Int); decide⟩
    (Spike.Lib.X64.WakePh.hw_fi hC)
  have hst : NodeW (fun s _ => SFactsSt2 (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) (ownGXW (Ly) aN) s Dt)
      (Spike.Lib.X64.PhRec.K (Ly) ⟨0, 0⟩) (Ly).exe (Ly).endPc R (DFrame R m0) (fN lbW cP cA mT .ts) :=
    fun s c hA => ⟨(hL s c hA).1 (hstD s c hA).1, (hstD s c hA).2⟩
  -- the other components
  have hI := Spike.Lib.X64.WakePh.instOkW hprog hlo aN (fun _ => False) hsite (rS := ⟨0, 0⟩)
  obtain ⟨-, -, hnx, -, -⟩ := refAbOk_spec hlab
  obtain ⟨hlc, hlm⟩ := Spike.Lib.X64.WakeRefSeg.lbl_of_toNat hl hcA hmT
  have hctl := Spike.Lib.X64.WakeSrcCtl.spawnSrc_ctl hsrc
  have hP := Spike.Lib.X64.WakeSrcCtl.placedSE_nodeMS (Λ := (Ly).Λ) (exe := (Ly).exe) (endPc := (Ly).endPc)
    (R := R) (F := DFrame R m0) (n := fN lbW cP cA mT .ts) hsrc ⟨by decide, by omega, by omega⟩
    ⟨by decide, by omega, by omega⟩ (fun σ c h => ⟨h.1, h.2.2⟩) hlc hlm
  have hW := Spike.Lib.X64.WakeWf.nodeW_wf (ar := Spike.Lib.X64.WakeOD.arW hp i) (p := wakeSrc)
    (Cl := Spike.Lib.X64.WakeOD.ClW hp i) (Ctx := fun _ _ _ => False)
    (lbl := Spike.Lib.X64ConsumerA.upd (L0T (Ly).Λ) l b)
    (lsize := Spike.Lib.X64ConsumerA.updN (Spike.Lib.X64WakeLoadT.ls0T ls0) l n) (fs := []) hst
    (Spike.Lib.X64.AllocG.nodeW_ab_fi hI hbP rfl rfl (by rw [Spike.Lib.X64.WakePh.okPc_eq hΛ]; exact hokc) hnx)
    (fun s c hAt => by
      obtain ⟨-, -, -, hpc, σ, hA, -, hJ⟩ := hAt
      exact ⟨Spike.Lib.X64ConsumerA.AcSt.of_ac (Spike.Lib.X64.WakePh.SpawnFail.ac_ts s σ c hJ hA hpc),
        fun _ h => h⟩)
    (fun _ h => h.2)
    (fun s c hAt => by
      obtain ⟨-, -, -, -, σ, -, -, hJ⟩ := id hAt
      obtain rfl := hJ.1
      exact ⟨⟨fun _ => hctl.1, (hP s c hAt).1, hctl.2⟩, fun _ h => h⟩)
    (Spike.Lib.X64.WakeWf.nodeW_noWrC (Spike.Lib.X64.AllocG.nodeW_noWr_fi hI hbP rfl rfl))
    (Spike.Lib.X64.WakeWf.nodeW_abortWf_off (Spike.Lib.X64.WakePh.CalWf.habtC hprog hlo hΛ hokcN))
  intro s c hAt
  have hps : refPc (pcOf s) = true := by unfold pcOf; rw [hAt.2.2.2.1]; exact hpc0
  obtain ⟨hX, hK⟩ := x1k1_ref asm hp i E ls0 hpa hlab (l := l) (b := b) (n := n) (c := c) hps
  refine ⟨⟨?_, hX⟩, hK⟩
  have := (hW s c hAt).1
  show Spike.Lib.X64.WakeWf.Wf _ _ _ _ _ _ _ _ _ _ _ _ s c []
  rw [Spike.Lib.X64.Flow.Worker.Wake.AbOffW.marks_target (Ly) hpL]
  exact this

set_option maxHeartbeats 1600000 in
/-- **`.spawnfail5`'s run ends at `scc_rt_abort`** with `ownG` `own2b … 0`
and both TCB words: `%rsp` on the pool (the band), the return address
`.Lwc_main.x5` pushed at `-72` (`raAt`, `Good2b`'s abort disjunct). -/
theorem fl_last (hlab : ∀ l x, codeLabel lo wakeCells l = some x → (Ly).lab l = Int64.ofNat x)
    {R : Region} {cP : Spike.Lib.Ctl} {cA mT : BitVec 64} (hband : BandOnP (Ly) R (-72) 8) (hlo' : R.lo ≤ -320)
    (hhi : 16 ≤ R.hi) (σ : Spike.Lib.X64.AS) (s : State) (m : MachineData)
    (hA : Abs R (arun lbW flB ⟨(fN lbW cP cA mT .fl).pc, (fN lbW cP cA mT .fl).o, σ⟩).so m
      (arun lbW flB ⟨(fN lbW cP cA mT .fl).pc, (fN lbW cP cA mT .fl).o, σ⟩).σ)
    (hs : s.st = (m, (arun lbW flB ⟨(fN lbW cP cA mT .fl).pc, (fN lbW cP cA mT .fl).o, σ⟩).pc))
    (hsp : SpAt R (-72) 8 s) :
    ownG (Ly) aN s = own2b (Ly) aN 0 ∧ Cst (Ly) (tM (Ly)) (tW (Ly)) s := by
  have hoE : (fN lbW cP cA mT .fl).o = oW := rfl
  have hpE : (fN lbW cP cA mT .fl).pc = lbW flL := rfl
  rw [hoE, hpE, Spike.Lib.X64.WakePh.SpawnFail.flB_run] at hA hs
  obtain ⟨-, -, -, oAb, oTw, oX1, -, -, -, -, -, -, hx1, hat, h0⟩ := refRange
  have e8 := lab_clN hlab oAb (L := Ly)
  have e9 := lab_clN hlab oTw (L := Ly)
  have hm : s.st.1 = m := by rw [hs]
  have hpc : pcOf s = ((Ly).lab "scc_rt_abort").toBitVec.toNat := by unfold pcOf; rw [hs]
  have hpool : spPool (Ly) s := by
    obtain ⟨k, hk1, hk2, hk⟩ := hsp
    unfold spPool; rw [hk]; exact hband k hk1 hk2
  have hin : pcOf s ∈ Spike.Lib.X64.WakePh.raSp (Ly) := by rw [hpc]; simp [Spike.Lib.X64.WakePh.raSp, abFns]
  have hrA : raAddr (Ly) s = s.st.1.regs.rsp.toBitVec := by simp only [raAddr, hin, ↓reduceIte]
  have hra : raAt (Ly) ".Lwc_main.x5" s := by
    unfold raAt
    rw [hrA, hm, rsp_of_abs hA]
    obtain ⟨j, hj1, hj2⟩ := hA.slot (-72) ⟨by decide, by omega, by omega⟩
    unfold privLoad
    rw [hm, hj1, Option.map_some, hj2, ← Spike.Lib.X64.WakeRefStub.raT_x23 hlab]
    simp only [Spike.Lib.upd_apply, ↓reduceIte, raT, Int64.toBitVec_add]; rfl
  have hinP : inPc (Ly) "scc_rt_abort" "scc_rt_thr_worker" s := by unfold inPc; rw [hpc, e8, e9]; omega
  have hg : Good2b (Ly) s := .inr (.inr ⟨hinP, hra, fun ⟨h5, _⟩ => by
    unfold raAt at h5 hra
    rw [h5] at hra
    exact Spike.Lib.X64.WakePh.ra_ne hlab (Option.some.inj hra)⟩)
  refine ⟨?_, Spike.Lib.X64.WakePh.ownS_of_self (.inl ⟨hpool, ?_⟩),
    Spike.Lib.X64.WakePh.ownSW_of_self (.inr (.inr ⟨hinP, hra⟩))⟩
  · rw [Spike.Lib.X64.WakePh.ownG_2b hlab hg, Spike.Lib.X64.WakePh.ph2b_eq, hpc, e8, h0]
  · rw [lab_clN hlab oX1, hpc, e8]; exact hx1

set_option maxHeartbeats 1600000 in
/-- **`RefBlk`**: the refusal path's `testq` row (`ts1`) and its three
blocks (`blk1`), inside `W1X` under no `K1W` move. -/
theorem refBlk (hpa : cellsOf asm = some o.prog) (hwp : cellsOf asm = some wakeCells) (hlo0 : Λ0.code.lo = lo)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true) {l : WeakMem.AllocLabel} {b n : Nat}
    (hl : L0T (Ly).Λ l = none) : RefBlk asm hp i E Dt Ctx ls0 l b n := by
  intro R m0 cP cA mT hpre
  obtain ⟨-, -, -, hR, hlo', hhi, hbase⟩ := id hpre
  have hprog := Spike.Lib.X64.WakeSrcCtl.prog_W hp i hpa hwp
  have hlo := Spike.Lib.X64.WakePh.StartPlaceLy.hlo_W hp i hlo0
  have hlab := Spike.Lib.X64WakeOAb.hlab_W hp i hpa hwp hlo0
  have hsite := PlaceWX.site_ofPlaceWX hp i
  have hΛ : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName := PlaceWX.abortLbl_of_placeWX (PlaceWX.link i hp)
  have hband := band_pre (L := Ly) hR hlo' hhi hbase
  have e21 := Spike.Lib.X64.WakePh.WcSp4W.lab_x21 hlab
  have e22 : lbW x22L = Int64.ofNat (cl x22L) := lab_cl hlab (by decide +kernel)
  have efl : lbW flL = Int64.ofNat (cl flL) := lab_cl hlab (by decide +kernel)
  have hin := Spike.Lib.X64.WakePh.SpawnFail.wake_failInB
  simp only [Spike.Lib.X64.WakePh.SpawnFail.failInB, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨-, hje⟩, hx22⟩, hfl⟩ := hin
  have hI2 := Spike.Lib.X64.WakePh.instOk2bP hprog hlo aN (rS := ⟨0, 0⟩) hsite
  obtain ⟨hjeA, hx22A, -, hflnx, habE⟩ := refAbOk_spec hlab
  have hoff56 : R.Off (-56) := ⟨by decide, by omega, by omega⟩
  refine ⟨ts1 asm hp i E Dt Ctx ls0 hpa hwp hlo0 hA13 hl hpre, ?_, ?_, ?_⟩
  · -- the `je`, not taken
    have hpE : (fN lbW cP cA mT .je).pc = lbW x21L + 51 := rfl
    have hoE : (fN lbW cP cA mT .je).o = oW := rfl
    refine blk1 asm hp i E Dt Ctx ls0 hpa hwp hlo0 hA13 hl hpre (lb := x21L) (k := 51) hje rfl
      (by rw [hoE]; decide) (by decide) (by decide) (fun j hj => by rw [hpE, e21]; revert j; decide +kernel)
      (fun j hj => by rw [hoE]; revert j; decide)
      (Spike.Lib.X64.AllocG.blkW_ab hI2 (lo := -72) (hi := 16) (dead := fun _ => false) (ra := 0)
        (by rw [hprog]; exact hje) rfl
        (by rw [hoE]; decide) hR (by omega) (by omega) (Spike.Lib.X64.WakePh.refPh_je hΛ hlab)
        (fun _ _ _ k hk hr => (Spike.Lib.X64Consumer.noRet_false (by decide) k hk hr).elim) (fun _ _ _ => rfl)
        hjeA)
      (fun s σ c j m hJ hj hA => Spike.Lib.X64.WakePh.SpawnFail.ac_je' s σ c j m hJ hj hA)
      (Spike.Lib.X64.WakeSrcCtl.keeps_fN _ (by simp)) (fun σ c h => ⟨h.1, h.2.2.1⟩) ?_
    intro σ c hJ s m _ hs hsp
    have hq : refPc (pcOf s) = true := by
      unfold pcOf
      rw [hs, hoE, hpE, Spike.Lib.X64.WakePh.Parent.jeB_run]
      simp only [hJ.2.2.2, Bool.false_eq_true, ite_false]
      rw [e21]
      decide +kernel
    exact ⟨own_ref hlab hq, cls_ref hlab hband s hq hsp⟩
  · -- `.x22`, the `jl` taken
    have hpE : (fN lbW cP cA mT .x22).pc = lbW x22L := rfl
    have hoE : (fN lbW cP cA mT .x22).o = oW := rfl
    refine blk1 asm hp i E Dt Ctx ls0 hpa hwp hlo0 hA13 hl hpre (lb := x22L) (k := 0) hx22
      (Spike.Lib.X64.Flow.ofNat_zero' _) (by rw [hoE]; decide) (by decide) (by decide)
      (fun j hj => by rw [hpE, e22]; revert j; decide +kernel)
      (fun j hj => by rw [hoE]; revert j; decide)
      (Spike.Lib.X64.AllocG.blkW_ab hI2 (lo := -72) (hi := 16) (dead := fun _ => false) (ra := 0)
        (by rw [hprog]; exact hx22)
        (Spike.Lib.X64.Flow.ofNat_zero' _) (by rw [hoE]; decide) hR (by omega) (by omega)
        (Spike.Lib.X64.WakePh.refPh_x22 hΛ hlab)
        (fun _ _ _ k hk hr => (Spike.Lib.X64Consumer.noRet_false (by decide) k hk hr).elim) (fun _ _ _ => rfl)
        hx22A)
      (fun s σ c j m hJ hj hA => Spike.Lib.X64.WakePh.SpawnFail.ac_x22 hoff56 s σ c j m hJ hj hA)
      (Spike.Lib.X64.WakeSrcCtl.keeps_fN _ (by simp)) (fun σ c h => ⟨h.1, h.2.2⟩) ?_
    intro σ c hJ s m _ hs hsp
    have hmsb : σ.regs.rax.toBitVec.msb = true := by
      have := hJ.2.1.slt; simpa [BitVec.slt_zero_eq_msb] using this
    have hq : refPc (pcOf s) = true := by
      unfold pcOf
      rw [hs, hoE, hpE, Spike.Lib.X64.WakePh.Parent.x22B_run]
      simp only [hmsb, ite_true]
      rw [efl]
      decide +kernel
    exact ⟨own_ref hlab hq, cls_ref hlab hband s hq hsp⟩
  · -- `.spawnfail5`: the call of `scc_rt_abort(5)`
    have hpE : (fN lbW cP cA mT .fl).pc = lbW flL := rfl
    have hoE : (fN lbW cP cA mT .fl).o = oW := rfl
    have hab : BlkW (fun s _ => AbSt (Spike.Lib.X64.PhRec.μ (Ly)) (Spike.Lib.X64.WriteAb.Ab (Ly).lab) s)
        (fun _ _ => False) (Ly).exe (Ly).endPc R (DFrame R m0) (fN lbW cP cA mT .fl) flB := by
      refine Spike.Lib.X64.AllocG.blkW_abG hI2 (l := flL) (off := 0) (lo := -72) (hi := 16) (dead := fun _ => false)
        (ra := 0)
        (by rw [hprog]; exact hfl) (Spike.Lib.X64.Flow.ofNat_zero' _) (by rw [hoE]; decide) hR (by omega)
        (by omega) (Spike.Lib.X64.WakePh.refPh_fl hΛ hlab)
        (fun _ _ _ k hk hr => (Spike.Lib.X64Consumer.noRet_false (by decide) k hk hr).elim) (fun _ _ _ => rfl) ?_
      intro σ c hJ k hk a ha s' _ _ hpc' hA'
      match k, hk with
      | 0, _ =>
        obtain ⟨a', ha', -, hterm⟩ := Spike.Lib.X64.okBlk_get (Ly).lab
          (am := ⟨(fN lbW cP cA mT .fl).pc, (fN lbW cP cA mT .fl).o, σ⟩) Spike.Lib.X64.WakePh.SpawnFail.flB_ok
          (k := 0) (by decide)
        rw [ha] at ha'
        cases ha'
        rw [Spike.Lib.X64.AI.tgt_of_not_term (hterm (by decide))] at hpc'
        refine Spike.Lib.X64.WriteAb.not_ab_of_pc ?_
        rw [hpc']
        exact hflnx
      | 1, _ =>
        -- the exit call: into the dispatcher with `%rdi = 5`, not the write abort's `4`
        have hc1 : Spike.Lib.X64.classify (flB[1]'(by decide)).1 = some (.call "scc_rt_abort") := rfl
        rw [hc1] at ha
        cases ha
        refine Spike.Lib.X64.AllocG.not_ab_abort (by rw [hpc', Spike.Lib.X64.BlockSpec.AI.tgt_call']) ?_ habE
        intro h4
        have hx := hA'.regs
        rw [Spike.Lib.X64.BlockSpec.AI.step_call'] at hx
        have h2 := Spike.Lib.X64.WakePh.SpawnFail.flB_run (Ly).lab (fN lbW cP cA mT .fl).pc σ
        have h3 := Spike.Lib.X64.arun_take_succ (Ly).lab (blk := flB) (k := 1) (by decide)
          ⟨(fN lbW cP cA mT .fl).pc, (fN lbW cP cA mT .fl).o, σ⟩
        rw [show flB.take (1 + 1) = flB from rfl] at h3
        have hrdi : (arun (Ly).lab flB ⟨(fN lbW cP cA mT .fl).pc, (fN lbW cP cA mT .fl).o, σ⟩).σ.regs.get64 .rdi
            = 5#64 := by
          rw [hoE, h2]
          simp [Reg64s.set64, Reg64s.get64]
        rw [h3] at hrdi
        generalize hb1 : flB[1] = d1 at hrdi hc1
        obtain ⟨d1, z1⟩ := d1
        simp only [Spike.Lib.X64.dstep] at hrdi hc1
        simp only [hc1, Spike.Lib.X64.BlockSpec.AI.step_call'] at hrdi
        rw [hx] at h4
        simp only [Reg64s.set64, Reg64s.get64] at h4 hrdi
        rw [hrdi] at h4
        exact absurd h4 (by decide)
    refine blk1 asm hp i E Dt Ctx ls0 hpa hwp hlo0 hA13 hl hpre (lb := flL) (k := 0) hfl
      (Spike.Lib.X64.Flow.ofNat_zero' _) (by rw [hoE]; decide) (by decide) (by decide)
      (fun j hj => by rw [hpE, efl]; revert j; decide +kernel)
      (fun j hj => by rw [hoE]; revert j; decide) hab
      (fun s σ c j m _ hj _ => Spike.Lib.X64.WakePh.SpawnFail.ac_fl s j m hj)
      (Spike.Lib.X64.WakeSrcCtl.keeps_fN _ (by simp)) (fun σ c h => ⟨h.1, h.2⟩) ?_
    intro σ c _ s m hA hs hsp
    exact fl_last hp i hlab hband hlo' hhi σ s m hA hs hsp

end Inst

end Spike.Lib.X64.WakeRefStub

/-- info: 'Spike.Lib.X64.WakeRefStub.refPc_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeRefStub.refPc_spec

/-- info: 'Spike.Lib.X64.WakeRefStub.own_ref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeRefStub.own_ref

/-- info: 'Spike.Lib.X64.WakeRefStub.cls_ref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeRefStub.cls_ref

/-- info: 'Spike.Lib.X64.WakeRefStub.band_pre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeRefStub.band_pre

/-- info: 'Spike.Lib.X64.WakeRefStub.refAbLabs_ok' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeRefStub.refAbLabs_ok

/-- info: 'Spike.Lib.X64.WakeRefStub.refAbOk_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeRefStub.refAbOk_ok

/-- info: 'Spike.Lib.X64.WakeRefStub.refAbOk_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeRefStub.refAbOk_spec

/-- info: 'Spike.Lib.X64.WakeRefStub.keep_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeRefStub.keep_test

/-- info: 'Spike.Lib.X64.WakeRefStub.clone_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeRefStub.clone_eq

/-- info: 'Spike.Lib.X64.WakeRefStub.x1k1_ref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeRefStub.x1k1_ref

/-- info: 'Spike.Lib.X64.WakeRefStub.blk1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeRefStub.blk1

/-- info: 'Spike.Lib.X64.WakeRefStub.ts1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeRefStub.ts1

/-- info: 'Spike.Lib.X64.WakeRefStub.fl_last' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeRefStub.fl_last

/-- info: 'Spike.Lib.X64.WakeRefStub.refBlk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeRefStub.refBlk

/-- info: 'Spike.Lib.X64.WakeRefStub.codeLabel_cl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeRefStub.codeLabel_cl

/-- info: 'Spike.Lib.X64.WakeRefStub.refRange' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeRefStub.refRange

/-- info: 'Spike.Lib.X64.WakeRefStub.lab_cl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeRefStub.lab_cl

/-- info: 'Spike.Lib.X64.WakeRefStub.lab_clN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeRefStub.lab_clN
