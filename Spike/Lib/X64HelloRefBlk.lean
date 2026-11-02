/-
**hello.w's refusal path inside the third level** (x86-64; the twin of `Spike/Lib/A64HelloRefBlk.lean`, the
hello twin of `Spike/Lib/X64WakeRefBlk.lean`): the `testq` row `ts` at `.x25 + 96`, the `je` block at
`.x25 + 99`, `.x26`'s block and `.spawnfail5`'s, inside `RootWX.W2H ∧ X2H` (the root's `W2I ∧ X2I`) under no
`TakeCKS` move. `W2H`'s `Wf` by `WakeWf.blkW_wf`/`nodeW_wf`: `SFactsSt2` at `ownGH` by `WcSp4W.blk_cH`/`node_cH`
at `own2bH … 0`, where `ownGH` agrees with it (`agreeBlkH`, `own_refH`); the write abort's phase kept
(`AllocG.blkW_ab`/`nodeW_ab_fi`, the targets off `abPcs` decided at the code labels, `refAbOkH`; `.spawnfail5`'s
call enters the dispatcher at `%rdi = 5`, `AllocG.not_ab_abort`); the nodes inside the threads abort phase `AcH`
(`SpawnFail.ac_ts`/`ac_je'`/`ac_x26`/`ac_fl`); the source's frames placed (`placedSE_blkMSS`/`placedSE_nodeMSS`).
`X2H` off the clone's pc and the take site (`x2H_off`).

- `clH`, `clOkH`, `codeLabel_clH`, `lab_clH`, `lab_clNH`: a code label's resolved address in hello's code;
  `refRangeH`: the decided facts at them.
- `refPcH`, `refPcH_spec`: a refusal pc, decided: in `[.x25 + 96, .stk)`, off the sites, at `ph2bH` `0`.
- `own_refH`: `ownGH` is `own2bH … 0` at a refusal pc.
- `refAbOkH`, `refAbOkH_ok`, `refAbOkH_spec`: the targets' check at the code labels.
- `placedSE_blkMSS`, `placedSE_nodeMSS`, `keeps_fNS`: the source placed at main's slots `MSS`.
- `blk1H`: one block; `ts1H`: the row; `fl_lastH`: `.spawnfail5`'s run's end; `refBlkH`: `RefO.BlkH`.

No absolute address appears in a statement here.

**Unlike AArch64** (forced by the x86-64 shape, as in `Spike/Lib/X64WakeRefBlk.lean`):
- `BlkH` is a row `ts` (a `NodeW`, the `testq`) and three blocks `je`, `x26`, `fl` (AArch64: the three blocks
  `cb`, `cl`, `fl`), so `ts1H` is new;
- the write abort's phase is `AllocG.blkW_ab` with a decided target check (`refAbOkH`; AArch64's
  `blkW_dispAbI` with `dChkAH`), the exit call's target the dispatcher at `%rdi = 5` (`not_ab_abort`; AArch64's
  `hE`);
- `.spawnfail5`'s run ends at `scc_rt_abort` with `.Lwc_main.x27` pushed at `-136` (`raAt`, a private word;
  AArch64: `x30At` of `.L22_wc_main.sp15`), so `Good2bH`'s abort disjunct is proved here (`fl_lastH`);
- the pcs are decided at the code labels (`clH`: `.x25`, `.stk`, `scc_rt_abort`, the take site, the clone's
  `syscall` at `.x25 + 94`, `refRangeH`), the blocks' `%rbp` frame bounds `[-136, 16)` (AArch64: `[-144, 0)`
  with `hal`), and main's slots `MSS` at `-8`, `-24`, `-32`, `-48`, `-40` (AArch64: `-144`, `-128`, `-120`,
  `-104`, `-112`).
-/
import Spike.Lib.X64HelloRefPre
import Spike.Lib.X64HelloRefPh
import Spike.Lib.X64HelloWcSp4W
import Spike.Lib.X64HelloOwnGEq
import Spike.Lib.X64HelloSpawnFailAC
import Spike.Lib.X64HelloH1ASrc
import Spike.Lib.X64HelloRootWX
import Spike.Lib.X64HelloH2Inv
import Spike.Lib.X64HelloSpawnPl
import Spike.Lib.X64HelloSpawnFailS
import Spike.Lib.X64HelloWcWf
import Spike.Lib.X64WakeRefBlk

namespace Spike.Lib.X64.HelloPh.RefBlkH

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib (Region FragS Arena)
open Spike.Lib.X64 (ND At BlkW NodeW DFrame Abs arun cellOff okBlk)
open Spike.Lib.X64.Rt (RuntimeLayout InstOk)
open Spike.Lib.X64ConsumerA (SFactsSt2 rsp_of_abs)
open Spike.Lib.X64ConsumerS (PlacedSE)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64.HelloPh (ownGH own2bH ph2bHC ph2bH_eq okC okPc_eq Good2bH ownGH_2b ClH instOk2bPH instOkH)
open Spike.Lib.X64.WakePh (inPc raAt raAddr raSp abFns)
open Spike.Lib.X64.Flow.Worker.Hello.SpawnFail (fNS MSS flB flL)
open Spike.Lib.X64.Flow.Worker.Hello.Parent (oP tsB jeB x26B x26L)
open Spike.Lib.X64.Flow.Worker.Hello.Child (x25L)
open Spike.Lib.X64.Flow.Ret0.StackTake (siteL)
open Spike.Lib.X64.ThreadsAb (raT)
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.X64HelloMainPreSrc (SpawnSrcH SlRep)
open Spike.Lib.X64WakeSrcDefs (mainTidLbl)
open Spike.Lib.X64.WakeSrcCtl (keepsSlot arun_slot_keep placeVal_slot_abs)
open Scc.Cert.Rt.X64 (blockAtB codeT codeT_eq code_field)
open SccCode (helloCells)
open Kraken.Promising.Lower.X64 (CellAt)
open Scc.Sem.X64 (privLoad)

/-! ## The refusal pcs -/

/-- **A code label's resolved address** in hello's code (`0` off it). -/
def clH (l : Label) : Nat := (codeT Spike.Lib.X64.HelloPh.lo helloCells l).getD 0

/-- `l` is a code label of hello's, below `2 ^ 63`. -/
def clOkH (l : Label) : Bool := (codeT Spike.Lib.X64.HelloPh.lo helloCells l).isSome && decide (clH l < 2 ^ 63)

theorem codeLabel_clH {l : Label} (h : clOkH l = true) :
    codeLabel Spike.Lib.X64.HelloPh.lo helloCells l = some (clH l) := by
  rw [← codeT_eq]
  unfold clOkH at h
  unfold clH
  cases hc : codeT Spike.Lib.X64.HelloPh.lo helloCells l with
  | none => simp [hc] at h
  | some x => rfl

/-- **The refusal path's facts at the code labels**: the labels laid out, `[.x25 + 96, .stk)` inside
`[.x25, .stk)` and past the take site and the clone's `syscall` (`.x25 + 94`), `scc_rt_abort` below
`scc_rt_thr_worker` and at `ph2bH` `0`, the two return addresses of the abort path different. -/
theorem refRangeH :
    clOkH x25L = true ∧ clOkH ".Lwc_main.stk" = true ∧ clOkH siteL = true ∧ clOkH "scc_rt_abort" = true ∧
      clOkH "scc_rt_thr_worker" = true ∧ clOkH ".Lwc_main.x27" = true ∧ clOkH ".Lscc_rt_alloc_tcb.x6" = true ∧
      clH siteL < clH x25L + 94 ∧ clH x25L + 96 < clH ".Lwc_main.stk" ∧
      clH "scc_rt_abort" < clH "scc_rt_thr_worker" ∧ ph2bHC (clH "scc_rt_abort") = 0 ∧
      clH ".Lwc_main.x27" ≠ clH ".Lscc_rt_alloc_tcb.x6" := by
  decide +kernel

/-- **A refusal pc**: past the clone's `syscall` and before `.stk` (`[.x25 + 96, .stk)`), off the sites, at
`ph2bH` `0`. -/
def refPcH (q : Nat) : Bool :=
  decide (clH x25L + 96 ≤ q ∧ q < clH ".Lwc_main.stk") && okC q && ph2bHC q == 0

theorem refPcH_spec {q : Nat} (h : refPcH q = true) :
    clH x25L + 96 ≤ q ∧ q < clH ".Lwc_main.stk" ∧ okC q = true ∧ ph2bHC q = 0 := by
  unfold refPcH at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

section Lab

variable {L : RuntimeLayout} {a : BitVec 64}
  (hlab : ∀ l x, codeLabel Spike.Lib.X64.HelloPh.lo helloCells l = some x → L.lab l = Int64.ofNat x)
include hlab

/-- **A code label's address** in the layout is `clH`'s. -/
theorem lab_clH {l : Label} (h : clOkH l = true) : L.lab l = Int64.ofNat (clH l) := hlab _ _ (codeLabel_clH h)

theorem lab_clNH {l : Label} (h : clOkH l = true) : (L.lab l).toBitVec.toNat = clH l := by
  have hb : clH l < 2 ^ 63 := by
    unfold clOkH at h; simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h.2
  rw [lab_clH hlab h]
  show (BitVec.ofNat 64 (clH l)).toNat = clH l
  rw [BitVec.toNat_ofNat]; omega

/-- **`ownGH` at a refusal pc** is `own2bH L a 0`. -/
theorem own_refH {s : State} (h : refPcH (pcOf s) = true) : ownGH L a s = own2bH L a 0 := by
  obtain ⟨h1, h2, -, h4⟩ := refPcH_spec h
  obtain ⟨o25, oStk, -⟩ := refRangeH
  have hg : Good2bH L s := .inr (.inl (by unfold inPc; rw [lab_clNH hlab o25, lab_clNH hlab oStk]; omega))
  rw [ownGH_2b hlab hg, ph2bH_eq, h4]

/-- **A refusal pc is off the take site** (at its label's address). -/
theorem ref_ne_site {q : Nat} (h : refPcH q = true) : q ≠ (L.lab siteL).toBitVec.toNat := by
  obtain ⟨h1, -, -, -⟩ := refPcH_spec h
  rw [lab_clNH hlab refRangeH.2.2.1]
  have := refRangeH.2.2.2.2.2.2.2.1
  omega

/-- **A refusal pc is off the clone's pc.** -/
theorem ref_ne_clone {q : Nat} (h : refPcH q = true) : q ≠ Spike.Lib.X64HelloPreA.clonePcH L := by
  obtain ⟨h1, -, -, -⟩ := refPcH_spec h
  have e : Spike.Lib.X64HelloPreA.clonePcH L = clH x25L + 94 := by
    show (L.lab x25L + 94).toBitVec.toNat = _
    rw [lab_clH hlab refRangeH.1]
    have := refRangeH.2.2.2.2.2.2.2.2.1
    have hb : clH x25L < 2 ^ 63 := by
      have h := refRangeH.1; unfold clOkH at h; simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h.2
    rw [show (94 : Int64) = Int64.ofNat 94 from rfl, ← Int64.ofNat_add]
    show (BitVec.ofNat 64 (clH x25L + 94)).toNat = _
    rw [BitVec.toNat_ofNat]; omega
  rw [e]; omega

end Lab

/-! ## The targets off the write abort's pcs -/

/-- The labels the targets' check reads. -/
def refAbLabsH : List String :=
  Spike.Lib.X64.AllocG.abLabs ++ Spike.Lib.LowerX64.blkLabs jeB ++ Spike.Lib.LowerX64.blkLabs x26B ++
    [x25L, x26L, flL]

theorem refAbLabsH_ok :
    refAbLabsH.all (fun x => (codeLabel Spike.Lib.X64.HelloPh.lo helloCells x).isSome) = true := by
  decide +kernel

/-- **The refusal path's targets off the write abort's pcs** at the code labels: the `je`'s and `.x26`'s
blocks', the `testq`'s and `movq $5, %rdi`'s next pcs, the exit call's target off every pc of `Ab` but the
dispatcher's prologue. -/
def refAbOkH : Bool :=
  let lab := Spike.Lib.LowerX64.labC Spike.Lib.X64.HelloPh.lo helloCells
  Spike.Lib.X64.AllocG.blkAbC lab (lab x25L + Int64.ofNat 99) 0 jeB &&
  Spike.Lib.X64.AllocG.blkAbC lab (lab x26L + Int64.ofNat 0) 0 x26B &&
  !(Spike.Lib.X64.WriteAb.abPcs lab).contains (lab x25L + Int64.ofNat 96 + Int64.ofNat 3) &&
  !(Spike.Lib.X64.WriteAb.abPcs lab).contains (lab flL + Int64.ofNat 0 + Int64.ofNat 7) &&
  !(Spike.Lib.X64.AllocG.abNoDispE lab).contains (lab "scc_rt_abort")

theorem refAbOkH_ok : refAbOkH = true := by decide +kernel

/-- **`refAbOkH` at any labels agreeing with the code labels.** -/
theorem refAbOkH_spec {lab : Label → Int64}
    (hlab : ∀ l x, codeLabel Spike.Lib.X64.HelloPh.lo helloCells l = some x → lab l = Int64.ofNat x) :
    Spike.Lib.X64ConsumerA.blkAb lab (lab x25L + Int64.ofNat 99) 0 jeB = true ∧
    Spike.Lib.X64ConsumerA.blkAb lab (lab x26L + Int64.ofNat 0) 0 x26B = true ∧
    lab x25L + Int64.ofNat 96 + Int64.ofNat 3 ∉ Spike.Lib.X64.WriteAb.abPcs lab ∧
    lab flL + Int64.ofNat 0 + Int64.ofNat 7 ∉ Spike.Lib.X64.WriteAb.abPcs lab ∧
    lab "scc_rt_abort" ∉ Spike.Lib.X64.AllocG.abNoDispE lab := by
  have hL : ∀ x ∈ refAbLabsH, lab x = Spike.Lib.LowerX64.labC Spike.Lib.X64.HelloPh.lo helloCells x :=
    fun x hx => by
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (List.all_eq_true.mp refAbLabsH_ok x hx)
      rw [hlab x y hy]; simp [Spike.Lib.LowerX64.labC, hy]
  have ha : ∀ l ∈ Spike.Lib.X64.AllocG.abLabs, lab l = Spike.Lib.LowerX64.labC Spike.Lib.X64.HelloPh.lo helloCells l :=
    fun l h => hL l (by simp only [refAbLabsH, List.mem_append]; exact .inl (.inl (.inl h)))
  have hj : ∀ l ∈ Spike.Lib.LowerX64.blkLabs jeB,
      lab l = Spike.Lib.LowerX64.labC Spike.Lib.X64.HelloPh.lo helloCells l :=
    fun l h => hL l (by simp only [refAbLabsH, List.mem_append]; exact .inl (.inl (.inr h)))
  have hx : ∀ l ∈ Spike.Lib.LowerX64.blkLabs x26B,
      lab l = Spike.Lib.LowerX64.labC Spike.Lib.X64.HelloPh.lo helloCells l :=
    fun l h => hL l (by simp only [refAbLabsH, List.mem_append]; exact .inl (.inr h))
  have e25 := hL x25L (by simp [refAbLabsH])
  have e26 := hL x26L (by simp [refAbLabsH])
  have efl := hL flL (by simp [refAbLabsH])
  have eab := ha "scc_rt_abort" (by simp [Spike.Lib.X64.AllocG.abLabs])
  have h := refAbOkH_ok
  simp only [refAbOkH, Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← Spike.Lib.X64.AllocG.blkAbC_eq, Spike.Lib.X64.AllocG.blkAbC_congr hj ha, e25]; exact h1
  · rw [← Spike.Lib.X64.AllocG.blkAbC_eq, Spike.Lib.X64.AllocG.blkAbC_congr hx ha, e26]; exact h2
  · rw [Spike.Lib.X64.AllocG.abPcs_congr ha, e25]; exact h3
  · rw [Spike.Lib.X64.AllocG.abPcs_congr ha, efl]; exact h4
  · rw [Spike.Lib.X64.AllocG.abNoDispE_congr ha, eab]; exact h5

/-! ## The source placed along the path -/

/-- **main's source placed at every block state**: the five packet words at the slots `MSS` names at the
node's entry, kept by the block (`hk`), represented under `lbl` (`hsl`, `hcA`, `hme`). -/
theorem placedSE_blkMSS {Λ : Scc.Sem.Layout} {lbl : Lbl} {l : WeakMem.AllocLabel} {ws : List TermRun.Word}
    {cP : Spike.Lib.Ctl} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {cA me : BitVec 64}
    {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {n : ND}
    {blk : List (Directive × Nat)} (hsrc : SpawnSrcH l ws cP)
    (hsl : SlRep lbl ws sl.1.toNat sl.2.1.toNat sl.2.2.1.toNat sl.2.2.2.toNat)
    (hcA : lbl l = some cA.toNat) (hme : lbl (mainTidLbl 2) = some me.toNat)
    (o0 : R.Off (-8)) (o2 : R.Off (-24)) (o3 : R.Off (-32)) (o4 : R.Off (-48)) (o5 : R.Off (-40))
    (hJ : ∀ σ c, n.J σ c → c = cP ∧ MSS sl cA me σ)
    (hk : ([-8, -24, -32, -48, -40] : List Int).all (fun j => keepsSlot j n.o blk) = true) :
    BlkW (fun s c => PlacedSE Λ lbl s c []) (fun _ _ => False) exe endPc R F n blk := by
  intro s σ c _ _ _ _ _ _ hj k _ m hA _
  obtain ⟨rfl, h0, h2, h3, h4, h5⟩ := hJ σ c hj
  obtain ⟨lr, rfl, hl, -, hw2, hw3⟩ := hsl
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hk
  obtain ⟨k0, k2, k3, k4, k5⟩ := hk
  refine ⟨Spike.Lib.X64.HelloPh.SpawnPl.placedSE_spawnAtH (.slot (R.addr (-8)).toNat)
    (.slot (R.addr (-24)).toNat) (.slot (R.addr (-32)).toNat) (.slot (R.addr (-48)).toNat)
    (.slot (R.addr (-40)).toNat) hsrc ?_ ?_ ?_ ?_ ?_, fun _ h => h⟩
  · refine ⟨_, placeVal_slot_abs hA o0, by decide, sl.1.toNat, by simp [Scc.Sem.wordAddr, hl], ?_⟩
    rw [arun_slot_keep _ _ blk ⟨n.pc, n.o, σ⟩ k k0, h0]; rfl
  · refine ⟨_, placeVal_slot_abs hA o2, by decide, ?_⟩
    rw [arun_slot_keep _ _ blk ⟨n.pc, n.o, σ⟩ k k2, h2]; exact hw2
  · refine ⟨_, placeVal_slot_abs hA o3, by decide, ?_⟩
    rw [arun_slot_keep _ _ blk ⟨n.pc, n.o, σ⟩ k k3, h3]; exact hw3
  · exact ⟨_, placeVal_slot_abs hA o4, by rw [arun_slot_keep _ _ blk ⟨n.pc, n.o, σ⟩ k k4, h4]; exact hcA⟩
  · exact ⟨_, placeVal_slot_abs hA o5, by rw [arun_slot_keep _ _ blk ⟨n.pc, n.o, σ⟩ k k5, h5]; exact hme⟩

/-- **main's source placed at a row's states**: the five packet words at the slots `MSS` names. -/
theorem placedSE_nodeMSS {Λ : Scc.Sem.Layout} {lbl : Lbl} {l : WeakMem.AllocLabel} {ws : List TermRun.Word}
    {cP : Spike.Lib.Ctl} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {cA me : BitVec 64}
    {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {n : ND}
    (hsrc : SpawnSrcH l ws cP) (hsl : SlRep lbl ws sl.1.toNat sl.2.1.toNat sl.2.2.1.toNat sl.2.2.2.toNat)
    (hcA : lbl l = some cA.toNat) (hme : lbl (mainTidLbl 2) = some me.toNat)
    (o0 : R.Off (-8)) (o2 : R.Off (-24)) (o3 : R.Off (-32)) (o4 : R.Off (-48)) (o5 : R.Off (-40))
    (hJ : ∀ σ c, n.J σ c → c = cP ∧ MSS sl cA me σ) :
    NodeW (fun s c => PlacedSE Λ lbl s c []) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨-, -, -, -, σ, hA, -, hj⟩
  obtain ⟨rfl, h0, h2, h3, h4, h5⟩ := hJ σ c hj
  obtain ⟨lr, rfl, hl, -, hw2, hw3⟩ := hsl
  refine ⟨Spike.Lib.X64.HelloPh.SpawnPl.placedSE_spawnAtH (.slot (R.addr (-8)).toNat)
    (.slot (R.addr (-24)).toNat) (.slot (R.addr (-32)).toNat) (.slot (R.addr (-48)).toNat)
    (.slot (R.addr (-40)).toNat) hsrc ?_ ?_ ?_ ?_ ?_, fun _ h => h⟩
  · refine ⟨_, placeVal_slot_abs hA o0, by decide, sl.1.toNat, by simp [Scc.Sem.wordAddr, hl], ?_⟩
    rw [h0]; rfl
  · exact ⟨_, placeVal_slot_abs hA o2, by decide, by rw [h2]; exact hw2⟩
  · exact ⟨_, placeVal_slot_abs hA o3, by decide, by rw [h3]; exact hw3⟩
  · exact ⟨_, placeVal_slot_abs hA o4, by rw [h4]; exact hcA⟩
  · exact ⟨_, placeVal_slot_abs hA o5, by rw [h5]; exact hme⟩

/-- The three blocks keep the packet's five slots (`.x26` stores only to `-120`). -/
theorem keeps_fNS : ∀ blk ∈ [jeB, x26B, flB],
    ([-8, -24, -32, -48, -40] : List Int).all (fun j => keepsSlot j oP blk) = true := by
  decide +kernel

section Gen

variable {L : RuntimeLayout} (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = Spike.Lib.X64.HelloPh.lo)
  (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeLabel Spike.Lib.X64.HelloPh.lo helloCells l = some x → L.lab l = Int64.ofNat x)
  {a : BitVec 64} {ar : Arena} {Dt : State → Prop} {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize}
  {endX : Int64} {lbl' : Lbl} {lsize' : Lsize}

include hp hlo hΛ hlab

set_option maxHeartbeats 1600000 in
/-- **One refusal block inside `W2H ∧ X2H`**, no `TakeCKS` move: its pcs refusal pcs (`hq`), the write abort's
phase kept (`hab`), its states in `AcH` (`hac`), its controls not a `ret` with their runs well formed (`hJ`), its
frames placed (`hpl`), `ownGH` `own2bH … 0` where its run ends (`hlast`). -/
theorem blk1H {R : Region} {F : MachineData → Prop} (hR : R.OK) {blo : Int} (hRlo : R.lo ≤ blo)
    (hhi : 16 ≤ R.hi) {nd : ND} {blk : List (Directive × Nat)} {lb : Label} {k : Nat}
    (hb : blockAtB helloCells lb k blk = true) (he : L.lab lb + Int64.ofNat k = nd.pc)
    (hok : okBlk blo 16 nd.o blk = true)
    (hcls : (blk.all fun dz => (Spike.Lib.X64.classify dz.1).isSome) = true)
    (hnr : Spike.Lib.X64Consumer.noRetBlk blk = true)
    (hq : ∀ j < blk.length, refPcH (nd.pc + Int64.ofNat (cellOff blk j)).toBitVec.toNat = true)
    (hab : BlkW (fun s _ => Spike.Lib.X64ConsumerA.AbSt (Spike.Lib.X64.PhRec.μ L) (Spike.Lib.X64.WriteAb.Ab L.lab) s)
      (fun _ _ => False) L.exe L.endPc R F nd blk)
    (hac : ∀ (s : State) σ c j m, nd.J σ c → j < blk.length →
      Abs R (arun L.lab (blk.take j) ⟨nd.pc, nd.o, σ⟩).so m (arun L.lab (blk.take j) ⟨nd.pc, nd.o, σ⟩).σ →
      Spike.Lib.X64.Hello.ThreadsAb.AcH L.lab Spike.Lib.X64.HelloPh.StartWf.pfxM
        { s with st := (m, nd.pc + Int64.ofNat (cellOff blk j)) })
    (hJ : ∀ σ c, nd.J σ c → (∀ a, c.term ≠ .ret a) ∧ Spike.Lib.X64.WakeWf.RunWf helloSrc c [])
    (hpl : BlkW (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F nd blk)
    (hlast : ∀ σ c, nd.J σ c → ∀ (s : State) m,
      Abs R (arun L.lab blk ⟨nd.pc, nd.o, σ⟩).so m (arun L.lab blk ⟨nd.pc, nd.o, σ⟩).σ →
      s.st = (m, (arun L.lab blk ⟨nd.pc, nd.o, σ⟩).pc) → ownGH L a s = own2bH L a 0) :
    BlkW (fun s c => RootWX.W2H L a ar helloSrc Dt (ClH L) Ctx lbl lsize s c [] ∧
        Spike.Lib.X64HelloH2Inv.X2H L (L.lab siteL) endX lbl' lsize' s c [])
      (Spike.Lib.X64ConsumerA.TakeCKS (L.lab siteL) (ClH L)) L.exe L.endPc R F nd blk := by
  have hsite := Spike.Lib.X64.HelloPh.siteH hp hlo hlab
  have hbP : blockAtB L.prog lb k blk = true := by rw [hp]; exact hb
  have hcode : ∀ s : State, s.exe = L.exe → s.endPc = L.endPc → Spike.Lib.X64.CodeAt s nd.pc blk :=
    code_field L.lays rfl hbP he
  have hns : ∀ j < blk.length, (nd.pc + Int64.ofNat (cellOff blk j)).toBitVec.toNat ≠ 4200314 := fun j hj => by
    have := ref_ne_site hlab (hq j hj)
    rwa [Spike.Lib.X64.HelloPh.WcSp4W.lab_siteH hlab, Spike.Lib.X64.HelloPh.WcSp4W.site_toNatH] at this
  have hag := Spike.Lib.X64.HelloPh.WcSp4W.agreeBlkH (a := a) (F := F) hlab hsite hcode hok hR hRlo hhi hns
    (fun σ c _ j hj s m _ hs => own_refH hlab (by unfold pcOf; rw [hs]; exact hq j hj)) hlast
  have hokc : ∀ j < blk.length, okC (nd.pc + Int64.ofNat (cellOff blk j)).toBitVec.toNat = true :=
    fun j hj => (refPcH_spec (hq j hj)).2.2.1
  have hst := Spike.Lib.X64.HelloPh.WcSp4W.blk_cH hp hlo hΛ hsite (own2bH L a 0) (Λ := L.Λ)
    (rS := ⟨0, 0⟩) hbP he hok hR hRlo hhi hcls hnr hokc hag
  have hI2 := instOk2bPH hp hlo a (rS := ⟨0, 0⟩) hsite
  have hW := Spike.Lib.X64.WakeWf.blkW_wf (ar := ar) (p := helloSrc) (Cl := ClH L) (Ctx := Ctx) (lbl := lbl)
    (lsize := lsize) (fs := []) (Spike.Lib.X64.WakePh.CalWf.blkW_dt (Dt := Dt) hst) hab
    (fun s σ c _ _ _ _ _ _ hj j hk m hA _ =>
      ⟨Spike.Lib.X64ConsumerA.AcSt.of_ac (hac s σ c j m hj hk hA), fun _ h => h⟩)
    (fun _ h => h.2)
    (fun s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9 =>
      ⟨⟨fun _ => (hJ σ c a7).1, (hpl s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9).1, (hJ σ c a7).2⟩, fun _ h => h⟩)
    (Spike.Lib.X64.WakeWf.blkW_noWrC (Spike.Lib.X64.AllocG.blkW_noWr hI2 hbP he hok hR hRlo hhi))
    (Spike.Lib.X64.WakeWf.blkW_abortWf (fun j hj s _ _ h3 => (hI2.off s (by
      rw [okPc_eq hΛ]; unfold pcOf; rw [h3]; exact hokc j hj)).1))
  intro s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9
  have hqj := hq j hj
  have hc : pcOf { s with st := (m, nd.pc + Int64.ofNat (cellOff blk j)) } ≠ Spike.Lib.X64HelloPreA.clonePcH L :=
    ref_ne_clone hlab hqj
  have ha : pcOf { s with st := (m, nd.pc + Int64.ofNat (cellOff blk j)) } ≠ (L.lab siteL).toBitVec.toNat :=
    ref_ne_site hlab hqj
  refine ⟨⟨⟨rfl, (hW s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9).1⟩, Spike.Lib.X64HelloH2Inv.x2H_off hc ha⟩,
    Spike.Lib.X64.Flow.WakeWc.takeCKS_none (fun _ h => h.1) (fun h => ha (by unfold pcOf; rw [h])) hc⟩

set_option maxHeartbeats 1600000 in
/-- **The refusal path's `testq` row inside `W2H ∧ X2H`**, no `TakeCKS` move. -/
theorem ts1H {l : WeakMem.AllocLabel} {ws : List TermRun.Word} {R : Region} {m0 : MachineData} {cP : Spike.Lib.Ctl}
    {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {cA me : BitVec 64}
    (hpre : RefO.PreH L lbl l ws R cP sl cA me) :
    NodeW (fun s c => RootWX.W2H L a ar helloSrc Dt (ClH L) Ctx lbl lsize s c [] ∧
        Spike.Lib.X64HelloH2Inv.X2H L (L.lab siteL) endX lbl' lsize' s c [])
      (Spike.Lib.X64ConsumerA.TakeCKS (L.lab siteL) (ClH L)) L.exe L.endPc R (DFrame R m0)
      (fNS L.lab cP sl cA me .ts) := by
  obtain ⟨hsrc, hsl, hcA, hme, hR, -, hRlo, hhi, -⟩ := hpre
  have hsite := Spike.Lib.X64.HelloPh.siteH hp hlo hlab
  have e25 := lab_clH hlab refRangeH.1 (L := L)
  have hin := Spike.Lib.X64.Flow.Worker.Hello.SpawnFail.hello_failInB
  simp only [Spike.Lib.X64.Flow.Worker.Hello.SpawnFail.failInB, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨hts, -⟩, -⟩, -⟩ := hin
  have hbW : blockAtB helloCells x25L 96 [(Spike.Lib.X64.FI.toDir (.test_rr .rax .rax), 3)] = true := hts
  have hbP : blockAtB L.prog x25L 96 [(Spike.Lib.X64.FI.toDir (.test_rr .rax .rax), 3)] = true := by
    rw [hp]; exact hbW
  have hpcE : (fNS L.lab cP sl cA me .ts).pc = L.lab x25L + Int64.ofNat 96 := rfl
  have hpc0 : refPcH (fNS L.lab cP sl cA me .ts).pc.toBitVec.toNat = true := by rw [hpcE, e25]; decide +kernel
  have hpc3 : refPcH ((fNS L.lab cP sl cA me .ts).pc + Int64.ofNat 3).toBitVec.toNat = true := by
    rw [hpcE, e25]; decide +kernel
  have hokc : okC (L.lab x25L + Int64.ofNat 96).toBitVec.toNat = true := (refPcH_spec hpc0).2.2.1
  have hC : ∀ s c, At L.exe L.endPc R (DFrame R m0) (fNS L.lab cP sl cA me .ts) s c →
      CellAt s (Spike.Lib.X64.FI.toDir (.test_rr .rax .rax)) 3 := fun s c hAt => by
    obtain ⟨he, hn, -, hp', -⟩ := hAt
    exact (code_field L.lays rfl hbP rfl s he hn).cell0 rfl rfl hp'
  -- the state's facts at `ownGH`
  have hI0 := InstOk.const (instOkH hp hlo a (fun _ => False) hsite (rS := ⟨0, 0⟩)) (own2bH L a 0) False
  have hst0 := Spike.Lib.X64.HelloPh.WcSp4W.node_cH hlab hsite (o := own2bH L a 0) (z := 3)
    (n := fNS L.lab cP sl cA me .ts)
    (Spike.Lib.X64.Rt.nodeW_fi_pre hI0 (Λ := L.Λ) (rS := ⟨0, 0⟩) (lbl := fun _ => none) (F := DFrame R m0)
      hbP rfl rfl Spike.Lib.X64.WakePh.WcW.c0N_cfacts
      (by rw [okPc_eq hΛ]; exact hokc) (fun _ _ h => h) rfl)
    (by
      have := ref_ne_site hlab hpc0
      rwa [Spike.Lib.X64.HelloPh.WcSp4W.lab_siteH hlab, Spike.Lib.X64.HelloPh.WcSp4W.site_toNatH] at this)
    (fun s hs => own_refH hlab (by unfold pcOf; rw [hs]; exact hpc0))
    (fun s hs => own_refH hlab (by unfold pcOf; rw [hs]; exact hpc3))
    (fun s c hAt => by
      have hc := hC s c hAt
      obtain ⟨tr, hex, hsl⟩ := Spike.Lib.X64.exec_fi hc
      refine ⟨_, _, hc, fun w w' h => (by cases h), hex, fun s' hu => ?_⟩
      obtain ⟨_, rfl⟩ := Spike.Lib.X64.WakePh.Tcb2W.silent_leaf hsl hu; rfl)
  have hst := Spike.Lib.X64.WakePh.CalWf.nodeW_dt (Dt := Dt) hst0
  -- the other components
  have hI := instOk2bPH hp hlo a (rS := ⟨0, 0⟩) hsite
  obtain ⟨-, -, hnx, -, -⟩ := refAbOkH_spec hlab
  have hctl := Spike.Lib.X64.HelloH1A.spawnSrcH_ctl (p := helloSrc) hsrc
  have hP := placedSE_nodeMSS (Λ := L.Λ) (exe := L.exe) (endPc := L.endPc) (R := R) (F := DFrame R m0)
    (n := fNS L.lab cP sl cA me .ts) hsrc hsl hcA hme ⟨by decide, by omega, by omega⟩
    ⟨by decide, by omega, by omega⟩ ⟨by decide, by omega, by omega⟩ ⟨by decide, by omega, by omega⟩
    ⟨by decide, by omega, by omega⟩ (fun σ c h => ⟨h.1, h.2.2⟩)
  have hW := Spike.Lib.X64.WakeWf.nodeW_wf (ar := ar) (p := helloSrc) (Cl := ClH L) (Ctx := Ctx) (lbl := lbl)
    (lsize := lsize) (fs := []) hst
    (Spike.Lib.X64.AllocG.nodeW_ab_fi hI hbP rfl rfl (by rw [okPc_eq hΛ]; exact hokc) hnx)
    (fun s c hAt => by
      obtain ⟨-, -, -, hpc, σ, hA, -, hJ⟩ := hAt
      exact ⟨Spike.Lib.X64ConsumerA.AcSt.of_ac (Spike.Lib.X64.Flow.Worker.Hello.SpawnFail.ac_ts (lab := L.lab)
        (cP := cP) (cA := cA) (mT := me) s σ c ⟨hJ.1, hJ.2.1, ⟨hJ.2.2.2.2.2.1, hJ.2.2.2.2.2.2⟩⟩ hA hpc), fun _ h => h⟩)
    (fun _ h => h.2)
    (fun s c hAt => by
      obtain ⟨-, -, -, -, σ, -, -, hJ⟩ := id hAt
      obtain rfl := hJ.1
      exact ⟨⟨fun _ => hctl.1, (hP s c hAt).1, hctl.2⟩, fun _ h => h⟩)
    (Spike.Lib.X64.WakeWf.nodeW_noWrC (Spike.Lib.X64.AllocG.nodeW_noWr_fi hI hbP rfl rfl))
    (Spike.Lib.X64.WakeWf.nodeW_abortWf_off
      (Spike.Lib.X64.HelloPh.WcWf.habt_of_okPcOfH hp hlo (by rw [okPc_eq hΛ]; exact hokc)))
  intro s c hAt
  have hps : refPcH (pcOf s) = true := by unfold pcOf; rw [hAt.2.2.2.1]; exact hpc0
  have hc := ref_ne_clone hlab hps
  have ha := ref_ne_site hlab hps
  refine ⟨⟨⟨rfl, (hW s c hAt).1⟩, Spike.Lib.X64HelloH2Inv.x2H_off hc ha⟩,
    Spike.Lib.X64.Flow.WakeWc.takeCKS_none (fun _ h => h.1) (fun h => ha (by unfold pcOf; rw [h])) hc⟩

omit hp hlo hΛ in
/-- **`.spawnfail5`'s run ends at `scc_rt_abort`** with `ownGH` `own2bH … 0`: the return address `.Lwc_main.x27`
pushed at `-136` (`raAt`, `Good2bH`'s abort disjunct). -/
theorem fl_lastH {R : Region} {cP : Spike.Lib.Ctl} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64}
    {cA me : BitVec 64} (hRlo : R.lo ≤ -136) (hhi : 16 ≤ R.hi) (σ : Spike.Lib.X64.AS) (s : State) (m : MachineData)
    (hA : Abs R (arun L.lab flB ⟨(fNS L.lab cP sl cA me .fl).pc, (fNS L.lab cP sl cA me .fl).o, σ⟩).so m
      (arun L.lab flB ⟨(fNS L.lab cP sl cA me .fl).pc, (fNS L.lab cP sl cA me .fl).o, σ⟩).σ)
    (hs : s.st = (m, (arun L.lab flB ⟨(fNS L.lab cP sl cA me .fl).pc, (fNS L.lab cP sl cA me .fl).o, σ⟩).pc)) :
    ownGH L a s = own2bH L a 0 := by
  have hoE : (fNS L.lab cP sl cA me .fl).o = oP := rfl
  have hpE : (fNS L.lab cP sl cA me .fl).pc = L.lab flL := rfl
  rw [hoE, hpE, Spike.Lib.X64.Flow.Worker.Hello.SpawnFail.flB_run] at hA hs
  obtain ⟨-, -, -, oAb, oTw, o27, o6, -, -, hlt, h0, hne⟩ := refRangeH
  have e8 := lab_clNH hlab oAb (L := L)
  have e9 := lab_clNH hlab oTw (L := L)
  have hm : s.st.1 = m := by rw [hs]
  have hpc : pcOf s = (L.lab "scc_rt_abort").toBitVec.toNat := by unfold pcOf; rw [hs]
  have hin : pcOf s ∈ raSp L := by rw [hpc]; simp [raSp, abFns]
  have hrA : raAddr L s = s.st.1.regs.rsp.toBitVec := by simp only [raAddr, hin, ↓reduceIte]
  have hld : privLoad s (raAddr L s) = some (L.lab ".Lwc_main.x27").toBitVec := by
    rw [hrA, hm, rsp_of_abs hA]
    obtain ⟨j, hj1, hj2⟩ := hA.slot (-136) ⟨by decide, by omega, by omega⟩
    unfold privLoad
    rw [hm, hj1, Option.map_some, hj2, ← RefO.raT_x27H hlab]
    simp only [Spike.Lib.upd_apply, ↓reduceIte, raT, Int64.toBitVec_add]; rfl
  have hinP : inPc L "scc_rt_abort" "scc_rt_thr_worker" s := by unfold inPc; rw [hpc, e8, e9]; omega
  have hg : Good2bH L s := .inr (.inr ⟨hinP, hld, fun ⟨h6, _⟩ => by
    unfold raAt at h6
    have h' := Option.some.inj (hld.symm.trans h6)
    exact hne (by rw [← lab_clNH hlab o27, ← lab_clNH hlab o6, h'])⟩)
  rw [ownGH_2b hlab hg, ph2bH_eq, hpc, e8, h0]

set_option maxHeartbeats 1600000 in
/-- **`RefO.BlkH` at the third level**: `ts1H` at the `testq`, `blk1H` at the `je` (not taken), `.x26`'s block
(the `jl` taken) and `.spawnfail5`'s (its run ending at `scc_rt_abort` with `.x27`'s return address); the source
placed from `PreH`'s slice and slots (`placedSE_blkMSS`). -/
theorem refBlkH {l : WeakMem.AllocLabel} {ws : List TermRun.Word} :
    RefO.BlkH L lbl l ws (fun s c => RootWX.W2H L a ar helloSrc Dt (ClH L) Ctx lbl lsize s c [] ∧
        Spike.Lib.X64HelloH2Inv.X2H L (L.lab siteL) endX lbl' lsize' s c [])
      (Spike.Lib.X64ConsumerA.TakeCKS (L.lab siteL) (ClH L)) := by
  intro R m0 cP sl cA me hpre
  obtain ⟨hsrc, hsl, hcA, hme, hR, -, hRlo, hhi, -⟩ := id hpre
  have hsite := Spike.Lib.X64.HelloPh.siteH hp hlo hlab
  have hoff : ∀ k : Int, k % 8 = 0 → -384 ≤ k → k + 8 ≤ 16 → R.Off k := fun k h1 h2 h3 =>
    ⟨h1, by omega, by omega⟩
  have e25 := lab_clH hlab refRangeH.1 (L := L)
  have e26 : L.lab x26L = Int64.ofNat (clH x26L) := lab_clH hlab (by decide +kernel)
  have efl : L.lab flL = Int64.ofNat (clH flL) := lab_clH hlab (by decide +kernel)
  have hin := Spike.Lib.X64.Flow.Worker.Hello.SpawnFail.hello_failInB
  simp only [Spike.Lib.X64.Flow.Worker.Hello.SpawnFail.failInB, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨-, hje⟩, hx26⟩, hfl⟩ := hin
  have hI2 := instOk2bPH hp hlo a (rS := ⟨0, 0⟩) hsite
  obtain ⟨hjeA, hx26A, -, hflnx, habE⟩ := refAbOkH_spec hlab
  have hpl := fun (nd : ND) (blk : List (Directive × Nat)) (hJ' : ∀ σ c, nd.J σ c → c = cP ∧ MSS sl cA me σ) hk =>
    placedSE_blkMSS (Λ := L.Λ) (exe := L.exe) (endPc := L.endPc) (F := DFrame R m0)
      (n := nd) (blk := blk) hsrc hsl hcA hme (hoff _ (by decide) (by decide) (by decide))
      (hoff _ (by decide) (by decide) (by decide)) (hoff _ (by decide) (by decide) (by decide))
      (hoff _ (by decide) (by decide) (by decide)) (hoff _ (by decide) (by decide) (by decide)) hJ' hk
  have hJc : ∀ {P : Prop} (c : Spike.Lib.Ctl), c = cP ∧ P →
      (∀ a, c.term ≠ .ret a) ∧ Spike.Lib.X64.WakeWf.RunWf helloSrc c [] := by
    rintro P c ⟨rfl, -⟩; exact Spike.Lib.X64.HelloH1A.spawnSrcH_ctl hsrc
  refine ⟨ts1H hp hlo hΛ hlab hpre, ?_, ?_, ?_⟩
  · -- the `je`, not taken
    have hpE : (fNS L.lab cP sl cA me .je).pc = L.lab x25L + 99 := rfl
    have hoE : (fNS L.lab cP sl cA me .je).o = oP := rfl
    refine blk1H hp hlo hΛ hlab hR (blo := -128) (by omega) hhi (lb := x25L) (k := 99) hje rfl
      (by rw [hoE]; decide) (by decide) (by decide) (fun j hj => by rw [hpE, e25]; revert j; decide +kernel)
      (Spike.Lib.X64.AllocG.blkW_ab hI2 (lo := -128) (hi := 16) (dead := fun _ => false) (ra := 0)
        (by rw [hp]; exact hje) rfl
        (by rw [hoE]; decide) hR (by omega) hhi (Spike.Lib.X64.HelloPh.refPh_jeH hΛ hlab)
        (fun _ _ _ k hk hr => (Spike.Lib.X64Consumer.noRet_false (by decide) k hk hr).elim) (fun _ _ _ => rfl)
        hjeA)
      (fun s σ c j m hJ hj hA => Spike.Lib.X64.Flow.Worker.Hello.SpawnFail.ac_je' (cA := cA) (mT := me) s σ c j m
        ⟨hJ.1, hJ.2.1, ⟨hJ.2.2.1.2.2.2.1, hJ.2.2.1.2.2.2.2⟩, hJ.2.2.2⟩ hj hA)
      (fun σ c h => hJc c h) (hpl _ _ (fun σ c h => ⟨h.1, h.2.2.1⟩) (keeps_fNS _ (by simp))) ?_
    intro σ c hJ s m _ hs
    refine own_refH hlab ?_
    unfold pcOf
    rw [hs, hoE, hpE, Spike.Lib.X64.Flow.Worker.Hello.Parent.jeB_run]
    simp only [hJ.2.2.2, Bool.false_eq_true, ite_false]
    rw [e25]
    decide +kernel
  · -- `.x26`, the `jl` taken
    have hpE : (fNS L.lab cP sl cA me .x26).pc = L.lab x26L := rfl
    have hoE : (fNS L.lab cP sl cA me .x26).o = oP := rfl
    refine blk1H hp hlo hΛ hlab hR (blo := -128) (by omega) hhi (lb := x26L) (k := 0) hx26
      (Spike.Lib.X64.Flow.ofNat_zero' _) (by rw [hoE]; decide) (by decide) (by decide)
      (fun j hj => by rw [hpE, e26]; revert j; decide +kernel)
      (Spike.Lib.X64.AllocG.blkW_ab hI2 (lo := -128) (hi := 16) (dead := fun _ => false) (ra := 0)
        (by rw [hp]; exact hx26)
        (Spike.Lib.X64.Flow.ofNat_zero' _) (by rw [hoE]; decide) hR (by omega) hhi
        (Spike.Lib.X64.HelloPh.refPh_x26H hΛ hlab)
        (fun _ _ _ k hk hr => (Spike.Lib.X64Consumer.noRet_false (by decide) k hk hr).elim) (fun _ _ _ => rfl)
        hx26A)
      (fun s σ c j m hJ hj hA => Spike.Lib.X64.Flow.Worker.Hello.SpawnFail.ac_x26 (cA := cA) (mT := me)
        (hoff _ (by decide) (by decide) (by decide)) s σ c j m
        ⟨hJ.1, hJ.2.1, ⟨hJ.2.2.2.2.2.1, hJ.2.2.2.2.2.2⟩⟩ hj hA)
      (fun σ c h => hJc c h) (hpl _ _ (fun σ c h => ⟨h.1, h.2.2⟩) (keeps_fNS _ (by simp))) ?_
    intro σ c hJ s m _ hs
    have hmsb : σ.regs.rax.toBitVec.msb = true := by
      have := hJ.2.1.slt; simpa [BitVec.slt_zero_eq_msb] using this
    refine own_refH hlab ?_
    unfold pcOf
    rw [hs, hoE, hpE, Spike.Lib.X64.Flow.Worker.Hello.Parent.x26B_run]
    simp only [hmsb, ite_true]
    rw [efl]
    decide +kernel
  · -- `.spawnfail5`: the call of `scc_rt_abort(5)`
    have hpE : (fNS L.lab cP sl cA me .fl).pc = L.lab flL := rfl
    have hoE : (fNS L.lab cP sl cA me .fl).o = oP := rfl
    have hab : BlkW (fun s _ => Spike.Lib.X64ConsumerA.AbSt (Spike.Lib.X64.PhRec.μ L)
        (Spike.Lib.X64.WriteAb.Ab L.lab) s) (fun _ _ => False) L.exe L.endPc R (DFrame R m0)
        (fNS L.lab cP sl cA me .fl) flB := by
      refine Spike.Lib.X64.AllocG.blkW_abG hI2 (l := flL) (off := 0) (lo := -136) (hi := 16) (dead := fun _ => false)
        (ra := 0)
        (by rw [hp]; exact hfl) (Spike.Lib.X64.Flow.ofNat_zero' _) (by rw [hoE]; decide) hR (by omega)
        hhi (Spike.Lib.X64.HelloPh.refPh_flH hΛ hlab)
        (fun _ _ _ k hk hr => (Spike.Lib.X64Consumer.noRet_false (by decide) k hk hr).elim) (fun _ _ _ => rfl) ?_
      intro σ c hJ k hk a ha s' _ _ hpc' hA'
      match k, hk with
      | 0, _ =>
        obtain ⟨a', ha', -, hterm⟩ := Spike.Lib.X64.okBlk_get L.lab
          (am := ⟨(fNS L.lab cP sl cA me .fl).pc, (fNS L.lab cP sl cA me .fl).o, σ⟩)
          Spike.Lib.X64.Flow.Worker.Hello.SpawnFail.flB_ok (k := 0) (by decide)
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
        have h2 := Spike.Lib.X64.Flow.Worker.Hello.SpawnFail.flB_run L.lab (fNS L.lab cP sl cA me .fl).pc σ
        have h3 := Spike.Lib.X64.arun_take_succ L.lab (blk := flB) (k := 1) (by decide)
          ⟨(fNS L.lab cP sl cA me .fl).pc, (fNS L.lab cP sl cA me .fl).o, σ⟩
        rw [show flB.take (1 + 1) = flB from rfl] at h3
        have hrdi : (arun L.lab flB ⟨(fNS L.lab cP sl cA me .fl).pc, (fNS L.lab cP sl cA me .fl).o, σ⟩).σ.regs.get64
            .rdi = 5#64 := by
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
    refine blk1H hp hlo hΛ hlab hR (blo := -136) (by omega) hhi (lb := flL) (k := 0) hfl
      (Spike.Lib.X64.Flow.ofNat_zero' _) (by rw [hoE]; decide) (by decide) (by decide)
      (fun j hj => by rw [hpE, efl]; revert j; decide +kernel) hab
      (fun s _ _ j m _ hj _ => Spike.Lib.X64.Flow.Worker.Hello.SpawnFail.ac_fl (lab := L.lab) (cP := cP) (cA := cA)
        (mT := me) s j m hj)
      (fun σ c h => hJc c h) (hpl _ _ (fun σ c h => h) (keeps_fNS _ (by simp))) ?_
    intro σ c _ s m hA hs
    exact fl_lastH hlab (by omega) hhi σ s m hA hs

end Gen

end Spike.Lib.X64.HelloPh.RefBlkH

/-- info: 'Spike.Lib.X64.HelloPh.RefBlkH.refRangeH' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RefBlkH.refRangeH

/-- info: 'Spike.Lib.X64.HelloPh.RefBlkH.refAbOkH_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RefBlkH.refAbOkH_spec

/-- info: 'Spike.Lib.X64.HelloPh.RefBlkH.own_refH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RefBlkH.own_refH

/-- info: 'Spike.Lib.X64.HelloPh.RefBlkH.blk1H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RefBlkH.blk1H

/-- info: 'Spike.Lib.X64.HelloPh.RefBlkH.ts1H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RefBlkH.ts1H

/-- info: 'Spike.Lib.X64.HelloPh.RefBlkH.fl_lastH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RefBlkH.fl_lastH

/-- info: 'Spike.Lib.X64.HelloPh.RefBlkH.refBlkH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RefBlkH.refBlkH
