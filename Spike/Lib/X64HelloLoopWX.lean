/-
**`wc_waitLoop`'s per-node obligations at any return label** (x86-64): the obligations of
`X64WaitLoopWX.LoopWX xl` (the loop with the label after the park call, `xl`, a parameter) at each conjunct
of main's post-spawn state predicate (`X64HelloMainInv.mainWRH`, which is `X64WakeInst.mainWR`), for any
listing `cells` whose loop passes `waitInX xl`. Every proof step is the one wake's `LoopW` uses at
`.Lwc_waitLoop.x16` (`X64WakeMainW.loopW_main`, `X64WakeMainR.loopW_relW`, `X64WakeMainL.loopW_ctl`,
`X64WakeMainS.loopW_sys`, `X64WakeMainF.loopW_flag`), with the nodes `NX xl`, the tail node `x16NX xl`
and the byte runs `waitRunsL xl`, `flagRunsL xl` (`X64HelloRunsOff`).

- `LoopWX.and`: two predicates' `LoopWX` combine.
- `loopWX_main`: `LoopWX` at `X64WakeInst.mainW` (pcs off the exits, source off `wlRet` and placed).
- `loopWX_relW`: at `RelWS`; `loopWX_ctl`: at any control predicate holding of `c0` and past the load;
  `loopWX_sys`: at `MainSys`; `loopWX_flag`: at `FlagW`.
- `parkGWX_flag`: `scc_rt_park`'s `ParkGW` at `FlagW` with the flag runs `flagRunsL xl`.

## Differences from the AArch64 version

- AArch64 states the loop obligations once, generic in the function's label prefix (`A64WakeMainW`,
  `A64WakeMainR`, `A64WakeMainL`, `A64WakeMainS`, `A64WakeMainF` over `A64WaitLoop`'s `pfx`), so hello reuses
  wake's lemmas. x86-64's wake lemmas are stated at wake's tail label `.Lwc_waitLoop.x16` (`X64WaitLoop.N`);
  hello's loop returns from the park at `.Lwc_waitLoop.x20`, so the lemmas are restated here over
  `X64WaitLoopWX.LoopWX xl`, generic in `xl` and the listing (`waitInX xl cells`).
- No `tlsW_*`: x86-64's limit load is the prologue's `w2` node, covered by each lemma's `pro` field
  (`loopWX_flag`'s premise `htp8`).
- The park's obligations other than `FlagW`'s need no restatement: `scc_rt_park`'s `ParkGW` lemmas are generic
  in the routine's code (`Park.Code`), and `seg_parkCallWX`'s park node `NX xl … .park` is wake's `N … .park` by
  definition. `X64WakeMainF.parkGW_flag` takes the flag runs at wake's `flagRuns` (which name `.x16`), so
  `parkGWX_flag` restates it at `flagRunsL xl`.
- Not twinned (unreachable from the AArch64 root, so twins only live constants): none; the file has no single
  AArch64 counterpart.
-/
import Spike.Lib.X64WaitLoopWX
import Spike.Lib.X64WakeMainW
import Spike.Lib.X64HelloRunsOff

namespace Spike.Lib.X64HelloLoopWX

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Scc.Sem (ValRep LocRep)
open Spike.Lib (Region)
open Spike.Lib.X64 Spike.Lib.X64.Flow
open Scc.Cert.Rt.X64 (Lays endOf code_field label_labelGapB)
open Spike.Lib.X64.WaitLoop
open Spike.Lib.X64.WaitLoopX (NX x16NX waitInX LoopWX)
open Spike.Lib.X64.HelloRunsOff (waitRunsL flagRunsL)
open Spike.Lib.X64WakeOff (PcOffA RunsOffA RunsNe pcOffA_add pcOffA_at)
open Spike.Lib.X64WakeInst (mainW)
open Spike.Lib.X64.WideKeep (WideX)
open Spike.Lib.X64WakeMainW (blkW_main nodeW_main placed_c0 placed_past placeVal_cell arun_one pro_rdi xS1_rdi
  xS2_rdi xS3_rdi b5_keep b7_slot b9_slot)
open Spike.Lib.X64WakeMainR (XProW.and xProW_relW relWS_load)
open Spike.Lib.X64WakeMainL (blkW_ctl nodeW_ctl xProW_ctl)
open Spike.Lib.X64WakeMainS (MainSys blkW_sys nodeW_sysCell xProW_sys)
open Spike.Lib.X64WakeMainF (FlagW flag0_of flagOff_past runsNe_at blkW_flag nodeW_flag xchg_noLoad syscall_noLoad)
open Spike.Lib.X64WakeM0 (wlBody)

set_option linter.unusedSimpArgs false

variable {xl : Label} {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {ms : MemSide isa} {c0 : Ctl} {x : String} {e : Expr} {ty : Ty} {A fp ra tp sp : BitVec 64}

/-- **Two predicates' `LoopWX` combine.** -/
theorem LoopWX.and {Rd : TermRun.Word → Prop} {W₁ W₂ : Frag isa}
    (h₁ : LoopWX xl W₁ ms exe endPc R F c0 x e ty Rd A fp ra tp sp)
    (h₂ : LoopWX xl W₂ ms exe endPc R F c0 x e ty Rd A fp ra tp sp) :
    LoopWX xl (fun s c => W₁ s c ∧ W₂ s c) ms exe endPc R F c0 x e ty Rd A fp ra tp sp where
  pro := XProW.and h₁.pro h₂.pro
  entry := h₁.entry.and h₂.entry
  ld := h₁.ld.and h₂.ld
  n5 := h₁.n5.and h₂.n5
  n6 := h₁.n6.and h₂.n6
  then1 := h₁.then1.and h₂.then1
  else2 := h₁.else2.and h₂.else2
  x16 := h₁.x16.and h₂.x16

/-! ## Inside `mainW` -/

set_option hygiene false in
/-- A block's pcs from `waitRunsL xl`: the run `(l, lo, hi)`, the node's offset `c` in it, the block. -/
local macro "pc_blk " l:term:max hi:term:max c:term:max b:term:max : tactic =>
  `(tactic| (intro k hk
             exact pcOffA_add (l := $l) (lo := 0) (hi := $hi) (c := $c) hruns (by simp [waitRunsL])
               (Nat.zero_le _) ((show ∀ k < ($b).length, $c + cellOff $b k < $hi by decide) k hk)
               (by simp only [NX, x16NX, xProN1, xProN2, xProN3, xProN4, Int64.add_assoc]
                   first | rfl | exact (ofNat_zero' _).symm | simp)))

variable {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat} {cv : String} {tyv : Ty}
  {w : TermRun.Word}

/-- **`wc_waitLoop`'s states are in `mainW`** at return label `xl` (`X64WakeMainW.loopW_main` over `LoopWX
xl`): the pcs off the exits (`hruns`, at `waitRunsL xl`), the states wide (`hwide`); the source at the load
reads only `cv` (`hfv0`), bound to the flag's locative `w` with base `A` (`hl`, `hloc`), past it only `x` and
`cv` (`hfvE`, `hxc`), and its continuation is not `wlRet` (`hE`). -/
theorem loopWX_main (hruns : RunsOffA (_root_.Executable.labels exe).label (waitRunsL xl))
    (hwide : ∀ s : State, s.exe = exe → s.decls = {} → WideX exe s)
    (hlo : R.lo ≤ -88) (hhi : 8 ≤ R.hi) (hc0 : c0.term ≠ WakeMLive.wlRet) (hE : e ≠ WakeMLive.wlRet)
    (hfv0 : ∀ y ∈ Scc.Sem.exprFv c0.term, y = cv) (hfvE : ∀ y ∈ Scc.Sem.exprFv e, y = x ∨ y = cv) (hxc : x ≠ cv)
    (hl : TermRun.lookupE c0.env cv = some (tyv, [w])) (hloc : LocRep lbl w.val A.toNat 0) :
    LoopWX xl (mainW (_root_.Executable.labels exe).label exe Λ lbl) ms exe endPc R F c0 x e ty
      (RdOne (ms := ms) lbl) A fp ra tp sp where
  pro := {
    w0 := by
      refine blkW_main (by pc_blk "wc_waitLoop" 31 0 xHead) hwide fun s σ c _ _ _ hJ k hk m hA' => ?_
      obtain ⟨rfl, hdi, -⟩ := hJ
      refine ⟨hc0, placed_c0 (pc := .reg (.r .rdi)) hfv0 hl hloc ?_⟩
      show some (m.regs.get64 .rdi).toNat = _
      rw [hA'.regs, pro_rdi _ _ _ _ (.inl rfl) hk]; exact congrArg _ (congrArg _ hdi)
    w1 := by
      refine blkW_main (by pc_blk "wc_waitLoop" 31 4 (xLea 16 5)) hwide fun s σ c _ _ _ hJ k hk m hA' => ?_
      obtain ⟨σ0, ⟨rfl, hdi, -⟩, rfl⟩ := hJ
      refine ⟨hc0, placed_c0 (pc := .reg (.r .rdi)) hfv0 hl hloc ?_⟩
      show some (m.regs.get64 .rdi).toNat = _
      rw [hA'.regs, pro_rdi _ _ _ _ (.inr (.inl rfl)) hk, xS1_rdi]; exact congrArg _ (congrArg _ hdi)
    w2 := by
      refine nodeW_main (pcOffA_at hruns (l := "wc_waitLoop") (lo := 0) (hi := 31) (c := 9)
        (by simp [waitRunsL]) (by omega) (by omega) (by simp only [xProN2, Int64.add_assoc]; first | rfl | simp))
        hwide fun s σ c _ hA _ hJ => ?_
      obtain ⟨σ0, ⟨rfl, hdi, -⟩, rfl⟩ := hJ
      refine ⟨hc0, placed_c0 (pc := .reg (.r .rdi)) hfv0 hl hloc ?_⟩
      show some (s.st.1.regs.get64 .rdi).toNat = _
      rw [hA.regs, xS2_rdi]; exact congrArg _ (congrArg _ hdi)
    w3 := by
      refine blkW_main (by pc_blk "wc_waitLoop" 31 18 (xCmp ".Lwc_waitLoop.stk" 3 2)) hwide
        fun s σ c _ _ _ hJ k hk m hA' => ?_
      obtain ⟨σ0, v, ⟨rfl, hdi, -⟩, -, rfl⟩ := hJ
      refine ⟨hc0, placed_c0 (pc := .reg (.r .rdi)) hfv0 hl hloc ?_⟩
      show some (m.regs.get64 .rdi).toNat = _
      rw [hA'.regs, pro_rdi _ _ _ _ (.inr (.inr (.inl rfl))) hk, xS3_rdi]; exact congrArg _ (congrArg _ hdi)
    w4 := by
      refine blkW_main (by pc_blk "wc_waitLoop" 31 23 (xFr 16 4 [(.rdi, -8, 4)])) hwide
        fun s σ c _ _ _ hJ k hk m hA' => ?_
      obtain ⟨σ0, v, ⟨rfl, hdi, -⟩, -, hreg, -⟩ := hJ
      refine ⟨hc0, placed_c0 (pc := .reg (.r .rdi)) hfv0 hl hloc ?_⟩
      show some (m.regs.get64 .rdi).toNat = _
      rw [hA'.regs, pro_rdi _ _ _ _ (.inr (.inr (.inr rfl))) hk, hreg, xS3_rdi]
      exact congrArg _ (congrArg _ hdi) }
  entry := by
    have o16 : R.Off (-16) := ⟨by decide, by omega, by omega⟩
    refine blkW_main (by pc_blk ".Lwc_waitLoop.entry" 29 0 b4) hwide fun s σ c _ _ _ hJ k hk m hA' => ?_
    obtain ⟨rfl, ⟨-, -, h16⟩, -, -⟩ := hJ
    refine ⟨hc0, placed_c0 (pc := .slot (R.addr (-16)).toNat) hfv0 hl hloc ?_⟩
    rw [placeVal_cell hA' o16 _ rfl, arun_one (by rfl) hk, h16]
  ld := by
    have o16 : R.Off (-16) := ⟨by decide, by omega, by omega⟩
    refine nodeW_main (pcOffA_at hruns (l := ".Lwc_waitLoop.entry") (lo := 0) (hi := 29) (c := 4)
      (by simp [waitRunsL]) (by omega) (by omega) (by simp only [NX]; first | rfl | simp)) hwide
      fun s σ c _ hA _ hJ => ?_
    obtain ⟨⟨rfl, ⟨-, -, h16⟩, -, -⟩, -⟩ := hJ
    refine ⟨hc0, placed_c0 (pc := .slot (R.addr (-16)).toNat) hfv0 hl hloc ?_⟩
    rw [placeVal_cell hA o16 _ rfl, h16]
  n5 := by
    have o16 : R.Off (-16) := ⟨by decide, by omega, by omega⟩
    refine blkW_main (by pc_blk ".Lwc_waitLoop.entry" 29 7 b5) hwide fun s σ c _ _ _ hJ k hk m hA' => ?_
    obtain ⟨⟨⟨-, -, h16⟩, -, -⟩, ⟨h1, w', ⟨-, hw'⟩, rfl⟩ | ⟨-, rfl⟩⟩ := hJ
    · refine ⟨hE, placed_past (pc := .slot (R.addr (-16)).toNat) (px := .reg (.r .rax)) hfvE hxc hl hloc ?_ hw' ?_⟩
      · erw [placeVal_cell hA' o16 _ rfl, (b5_keep _ _ _ hk).1, h16]
      · show some (m.regs.get64 .rax).toNat = _
        erw [hA'.regs, (b5_keep _ _ _ hk).2, show σ.regs.get64 .rax = 1#64 from h1]; rfl
    · refine ⟨hc0, placed_c0 (pc := .slot (R.addr (-16)).toNat) hfv0 hl hloc ?_⟩
      erw [placeVal_cell hA' o16 _ rfl, (b5_keep _ _ _ hk).1, h16]
  n6 := by
    have o16 : R.Off (-16) := ⟨by decide, by omega, by omega⟩
    refine blkW_main (by pc_blk ".Lwc_waitLoop.entry" 29 27 b6) hwide fun s σ c _ _ _ hJ k hk m hA' => ?_
    obtain ⟨rfl, ⟨-, -, h16⟩, -, -⟩ := hJ
    refine ⟨hc0, placed_c0 (pc := .slot (R.addr (-16)).toNat) hfv0 hl hloc ?_⟩
    rw [placeVal_cell hA' o16 _ rfl, arun_one (by rfl) hk, h16]
  then1 := by
    have o16 : R.Off (-16) := ⟨by decide, by omega, by omega⟩
    have o24 : R.Off (-24) := ⟨by decide, by omega, by omega⟩
    refine blkW_main (by pc_blk ".Lwc_waitLoop.then1" 12 0 b7) hwide fun s σ c _ _ _ hJ k hk m hA' => ?_
    obtain ⟨⟨⟨-, -, h16⟩, -, -⟩, ⟨w', ⟨-, hw'⟩, rfl⟩, h24⟩ := hJ
    refine ⟨hE, placed_past (pc := .slot (R.addr (-16)).toNat) (px := .slot (R.addr (-24)).toNat) hfvE hxc hl
      hloc ?_ hw' ?_⟩
    · erw [placeVal_cell hA' o16 _ rfl, b7_slot _ _ _ hk, h16]
    · erw [placeVal_cell hA' o24 _ rfl, b7_slot _ _ _ hk, h24]; rfl
  else2 := by
    have o16 : R.Off (-16) := ⟨by decide, by omega, by omega⟩
    refine blkW_main (by pc_blk ".Lwc_waitLoop.else2" 5 0 b8) hwide fun s σ c _ _ _ hJ k hk m hA' => ?_
    obtain ⟨rfl, ⟨-, -, h16⟩, -, -⟩ := hJ
    refine ⟨hc0, placed_c0 (pc := .slot (R.addr (-16)).toNat) hfv0 hl hloc ?_⟩
    rw [placeVal_cell hA' o16 _ rfl, arun_one (by rfl) hk, h16]
  x16 := by
    have o16 : R.Off (-16) := ⟨by decide, by omega, by omega⟩
    refine blkW_main (by pc_blk xl 10 0 b9) hwide fun s σ c _ _ _ hJ k hk m hA' => ?_
    obtain ⟨rfl, ⟨-, -, h16⟩, -, -⟩ := hJ
    refine ⟨hc0, placed_c0 (pc := .slot (R.addr (-16)).toNat) hfv0 hl hloc ?_⟩
    erw [placeVal_cell hA' o16 _ rfl, b9_slot _ _ _ hk, h16]

/-! ## Writes, controls and system calls -/

/-- **`wc_waitLoop`'s states are in `RelWS`** at return label `xl` (`X64WakeMainR.loopW_relW`). -/
theorem loopWX_relW [Executable.ValidLayout exe] {Rd : TermRun.Word → Prop} {cells : List (Directive × Nat)}
    {kp : Nat} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp) (hin : waitInX xl cells = true)
    (hR : R.OK) (hlo : R.lo ≤ -88) (hhi : 8 ≤ R.hi) :
    LoopWX xl (fun s _ => RelWS s) ms exe endPc R F c0 x e ty Rd A fp ra tp sp := by
  have hin' := hin
  simp only [waitInX, Bool.and_eq_true, and_assoc] at hin'
  obtain ⟨hpro, h4, hld, h5, h6, h7, h8, h9, -⟩ := hin'
  exact {
    pro := xProW_relW hp hend hpro hR (by have : (16 : Int64).toInt = 16 := by decide
                                          omega) (by omega) (by decide) (by decide)
    entry := blkW_relW b4_ok hR hlo hhi (code_field hp hend h4 (ofNat_zero' _))
    ld := nodeW_relW (code_field hp hend hld rfl) fun _ hc => relWS_load hc
    n5 := blkW_relW b5_ok hR hlo hhi (code_field hp hend h5 rfl)
    n6 := blkW_relW b6_ok hR hlo hhi (code_field hp hend h6 rfl)
    then1 := blkW_relW b7_ok hR hlo hhi (code_field hp hend h7 (ofNat_zero' _))
    else2 := blkW_relW b8_ok hR hlo hhi (code_field hp hend h8 (ofNat_zero' _))
    x16 := blkW_relW b9_ok hR hlo hhi (code_field hp hend h9 (ofNat_zero' _)) }

/-- **`wc_waitLoop`'s controls satisfy `P`** at return label `xl` (`X64WakeMainL.loopW_ctl`): each is `c0`
or past the load. -/
theorem loopWX_ctl {Rd : TermRun.Word → Prop} {P : Ctl → Prop} (h0 : P c0)
    (hP : ∀ c, Past c0 x e ty Rd c → P c) :
    LoopWX xl (fun _ c => P c) ms exe endPc R F c0 x e ty Rd A fp ra tp sp where
  pro := xProW_ctl fun _ _ hJ => by obtain ⟨rfl, -⟩ := hJ; exact h0
  entry := blkW_ctl fun _ _ hJ => by obtain ⟨rfl, -⟩ := hJ; exact h0
  ld := nodeW_ctl fun _ _ hJ => by obtain ⟨⟨rfl, -⟩, -⟩ := hJ; exact h0
  n5 := blkW_ctl fun _ c hJ => by
    obtain ⟨-, ⟨-, hp⟩ | ⟨-, rfl⟩⟩ := hJ
    · exact hP c hp
    · exact h0
  n6 := blkW_ctl fun _ _ hJ => by obtain ⟨rfl, -⟩ := hJ; exact h0
  then1 := blkW_ctl fun _ c hJ => by obtain ⟨-, hp, -⟩ := hJ; exact hP c hp
  else2 := blkW_ctl fun _ _ hJ => by obtain ⟨rfl, -⟩ := hJ; exact h0
  x16 := blkW_ctl fun _ _ hJ => by obtain ⟨rfl, -⟩ := hJ; exact h0

/-- **`wc_waitLoop`'s states are at no system call** at return label `xl` (`X64WakeMainS.loopW_sys`). -/
theorem loopWX_sys [Executable.ValidLayout exe] {Rd : TermRun.Word → Prop} {cells : List (Directive × Nat)}
    {kp : Nat} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp) (hin : waitInX xl cells = true)
    (hR : R.OK) (hlo : R.lo ≤ -88) (hhi : 8 ≤ R.hi) :
    LoopWX xl (fun s _ => MainSys s) ms exe endPc R F c0 x e ty Rd A fp ra tp sp := by
  have hin' := hin
  simp only [waitInX, Bool.and_eq_true, and_assoc] at hin'
  obtain ⟨hpro, h4, hld, h5, h6, h7, h8, h9, -⟩ := hin'
  exact {
    pro := xProW_sys hp hend hpro hR (by have : (16 : Int64).toInt = 16 := by decide
                                         omega) (by omega) (by decide) (by decide)
    entry := blkW_sys b4_ok hR hlo hhi (code_field hp hend h4 (ofNat_zero' _))
    ld := nodeW_sysCell (code_field hp hend hld rfl) fun _ _ h => by cases h
    n5 := blkW_sys b5_ok hR hlo hhi (code_field hp hend h5 rfl)
    n6 := blkW_sys b6_ok hR hlo hhi (code_field hp hend h6 rfl)
    then1 := blkW_sys b7_ok hR hlo hhi (code_field hp hend h7 (ofNat_zero' _))
    else2 := blkW_sys b8_ok hR hlo hhi (code_field hp hend h8 (ofNat_zero' _))
    x16 := blkW_sys b9_ok hR hlo hhi (code_field hp hend h9 (ofNat_zero' _)) }

/-! ## The flag load -/

set_option hygiene false in
/-- A block's `hX` from `flagRunsL xl`: the run `(l, lo, hi)`, the node's offset `c` in it, the block. -/
local macro "ne_blk " l:term:max lo:term:max hi:term:max c:term:max b:term:max : tactic =>
  `(tactic| (intro _ k _ _ hk _ hq
             have hb := (show ∀ k < ($b).length, $lo ≤ $c + cellOff $b k ∧ $c + cellOff $b k < $hi by decide) k hk
             exact absurd hq <| runsNe_at hflag (l := $l) (lo := $lo) (hi := $hi) (j := $c + cellOff $b k)
               (by simp [flagRunsL, Spike.Lib.X64.Flow.Park.parkRuns]) hb.1 hb.2
               (by rw [ofNat_add']
                   refine congrArg (· + Int64.ofNat (cellOff $b k)) ?_
                   all_goals try simp only [NX, x16NX, xProN1, xProN2, xProN3, xProN4, Spike.Lib.X64.Flow.Park.N,
                     Int64.add_assoc]
                   all_goals first | rfl | exact (ofNat_zero' _).symm | simp)))

set_option hygiene false in
/-- A node's `hX` from `flagRunsL xl`: the run `(l, lo, hi)`, the node's offset `c` in it. -/
local macro "ne_one " l:term:max lo:term:max hi:term:max c:term:max : tactic =>
  `(tactic| (intro s hAt hq
             obtain ⟨_, _, _, hpc, _⟩ := hAt
             exact absurd hq <| runsNe_at hflag (l := $l) (lo := $lo) (hi := $hi) (j := $c)
               (by simp [flagRunsL, Spike.Lib.X64.Flow.Park.parkRuns]) (by omega) (by omega)
               (by rw [hpc]
                   all_goals try simp only [NX, xProN2, Spike.Lib.X64.Flow.Park.N, Spike.Lib.X64.Flow.Park.pcSys,
                     Int64.add_assoc]
                   all_goals first | rfl | exact (ofNat_zero' _).symm | simp)))

set_option hygiene false in
/-- A park node's control is the loop's `c0`. -/
local macro "parkC" : term =>
  `(fun _ _ h => .inl (by first | exact h.1 | exact h.1.1 | exact h.1.1.1 | exact h.1.1.1.1))

variable {lsize : WeakMem.AllocLabel → Nat} {q : Int64} {a : At}

/-- **`wc_waitLoop`'s states are in `FlagW`** at return label `xl` (`X64WakeMainF.loopW_flag`), `q` the `n5`
node's pc: the loop's control at `wlBody` (`hwb`), its load's word `w` the untagged locative with base `A`
inside its label (`hloc`, `hin'`), every pc of `c0` but `q` off `q` (`hflag`, at `flagRunsL xl`), and the
prologue's limit word not the flag's (`htp8`). -/
theorem loopWX_flag [Executable.ValidLayout exe] {cells : List (Directive × Nat)} {kp : Nat}
    (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp) (hin : waitInX xl cells = true)
    (hR : R.OK) (hlo : R.lo ≤ -88) (hhi : 8 ≤ R.hi)
    (hq : q = (_root_.Executable.labels exe).label ".Lwc_waitLoop.entry" + Int64.ofNat 7)
    (hflag : RunsNe (_root_.Executable.labels exe).label q (flagRunsL xl))
    (hwb : c0.term = wlBody) (hterm : c0.term = .let_ x (.load true a) e)
    (hev : TermRun.evalAt c0.env a = some (ty, [w])) (hloc : LocRep lbl w.val A.toNat 0)
    (hin' : ∃ sa, w.val = .loc sa 0 ∧ sa.offset < lsize sa.label) (htp8 : tp + 8#64 ≠ A) :
    LoopWX xl (fun s c => FlagW lbl lsize q s c) ms exe endPc R F c0 x e ty
      (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A fp ra tp sp := by
  have h0 := flag0_of (lsize := lsize) hwb hterm hev hloc hin'
  have hP := fun c => flagOff_past (lbl := lbl) (ty := ty) (ms := ms) (c := c) hwb hterm
  have hnp : ¬ Past c0 x e ty (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) c0 := fun h =>
    (hP c0 h).1 hwb
  have hin2 := hin
  simp only [waitInX, Bool.and_eq_true, and_assoc] at hin2
  obtain ⟨hpro, h4, hld, h5, h6, h7, h8, h9, -⟩ := hin2
  have hpro2 := hpro
  simp only [prologueIn, Bool.and_eq_true, and_assoc] at hpro2
  obtain ⟨g0, p0, p1, p2, p3, p4, -⟩ := hpro2
  have e0 := label_labelGapB hp g0
  have e4 : (_root_.Executable.labels exe).label "wc_waitLoop" + 1 + 3 =
      (_root_.Executable.labels exe).label ".Lwc_waitLoop.chk" := by
    rw [e0, Int64.add_assoc]; rfl
  have hlo' : R.lo ≤ -8 - (16 : Int64).toInt := by
    have : (16 : Int64).toInt = 16 := by decide
    omega
  have hhi' : (0 : Int) ≤ R.hi := by omega
  refine {
    pro := {
      w0 := blkW_flag (xHead_ok (lo := -8 - (16 : Int64).toInt) (hi := 0) (by decide) (Int.le_refl _)) hR hlo'
        hhi' (code_field hp hend p0 (ofNat_zero' _)) h0 (fun _ _ hJ => .inl hJ.1)
        (by ne_blk "wc_waitLoop" 0 31 0 xHead)
      w1 := blkW_flag (xLea_ok (lo := -8 - (16 : Int64).toInt) (hi := 0) 16 5) hR hlo' hhi'
        (code_field hp hend p1 (by show _ = _ + 1 + 3; rw [e4, ofNat_zero'])) h0
        (fun _ _ ⟨_, hJ, _⟩ => .inl hJ.1) (by ne_blk "wc_waitLoop" 0 31 4 (xLea 16 5))
      w2 := nodeW_flag h0 (fun _ _ ⟨_, hJ, _⟩ => .inl hJ.1)
        (fun s ⟨he, hn, hdc, hpc, σ, hA, _, hJ⟩ kl k' hx => ?_) (by ne_one "wc_waitLoop" 0 31 9)
      w3 := blkW_flag (xCmp_ok (lo := -8 - (16 : Int64).toInt) (hi := 0) _ ".Lwc_waitLoop.stk" 3 2) hR hlo' hhi'
        (code_field hp hend p3 (by show _ = _ + 1 + 3 + _ + _; rw [e4, ofNat_add'])) h0
        (fun _ _ ⟨_, _, hJ, _⟩ => .inl hJ.1) (by ne_blk "wc_waitLoop" 0 31 18 (xCmp ".Lwc_waitLoop.stk" 3 2))
      w4 := blkW_flag (xFr_ok (lo := -8 - (16 : Int64).toInt) (hi := 0) 16 4 [(.rdi, -8, 4)] (by decide)) hR
        hlo' hhi' (code_field hp hend p4 (by
          show _ = _ + 1 + 3 + _ + _ + _ + _; rw [e4, ofNat_add', ofNat_add', ofNat_add'])) h0
        (fun _ _ ⟨_, _, hJ, _⟩ => .inl hJ.1) (by ne_blk "wc_waitLoop" 0 31 23 (xFr 16 4 [(.rdi, -8, 4)])) }
    entry := blkW_flag b4_ok hR hlo hhi (code_field hp hend h4 (ofNat_zero' _)) h0 (fun _ _ hJ => .inl hJ.1)
      (by ne_blk ".Lwc_waitLoop.entry" 0 7 0 b4)
    ld := nodeW_flag h0 (fun _ _ hJ => .inl hJ.1.1)
      (fun s ⟨he, hn, hdc, hpc, σ, hA, _, hJ⟩ kl k' hx => ?_) (by ne_one ".Lwc_waitLoop.entry" 0 7 4)
    n5 := blkW_flag b5_ok hR hlo hhi (code_field hp hend h5 rfl) h0
      (fun _ c hJ => by
        obtain ⟨-, ⟨-, hp⟩ | ⟨-, rfl⟩⟩ := hJ
        · exact .inr (hP c hp)
        · exact .inl rfl)
      (fun σ k m hJ hk hA hpq => by
        rcases k with _ | k
        · obtain ⟨-, ⟨-, hp⟩ | ⟨h1, -⟩⟩ := hJ
          · exact (hnp hp).elim
          · rw [hA.regs]; exact h1
        · have hb := (show ∀ k < b5.length, 0 < k → 8 ≤ 7 + cellOff b5 k ∧ 7 + cellOff b5 k < 29 by decide)
            (k + 1) hk (Nat.succ_pos _)
          refine absurd hpq (runsNe_at hflag (l := ".Lwc_waitLoop.entry") (lo := 8) (hi := 29)
            (by simp [flagRunsL]) hb.1 hb.2 ?_)
          rw [ofNat_add']; simp only [NX]; rfl)
    n6 := blkW_flag b6_ok hR hlo hhi (code_field hp hend h6 rfl) h0 (fun _ _ hJ => .inl hJ.1)
      (by ne_blk ".Lwc_waitLoop.entry" 8 29 27 b6)
    then1 := blkW_flag b7_ok hR hlo hhi (code_field hp hend h7 (ofNat_zero' _)) h0
      (fun _ c hJ => .inr (hP c hJ.2.1)) (fun _ _ _ hJ => (hnp hJ.2.1).elim)
    else2 := blkW_flag b8_ok hR hlo hhi (code_field hp hend h8 (ofNat_zero' _)) h0 (fun _ _ hJ => .inl hJ.1)
      (by ne_blk ".Lwc_waitLoop.else2" 0 5 0 b8)
    x16 := blkW_flag b9_ok hR hlo hhi (code_field hp hend h9 (ofNat_zero' _)) h0 (fun _ _ hJ => .inl hJ.1)
      (by ne_blk xl 0 10 0 b9) }
  -- the prologue's limit load `movq %fs:8, %r11`: `tp + 8`, not the flag's word
  · have hc : CellAt s (fsDir .r11 8) 9 :=
      (code_field hp hend p2 (by show _ = _ + 1 + 3 + _; rw [e4]) s he hn).cell0 rfl rfl hpc
    obtain ⟨σ0, hJ0, rfl⟩ := hJ
    have ha : fsAddr s 9 { base := none, idx := none, disp := .int64 8 } = tp + 8#64 := by
      simp [fsAddr, eaddr, AddrExpr.interp, ConstExpr.interp, hA.regs, xS2, xS1, hdRegs, Reg64s.set64,
        hJ0.2.2.2.2.2]
    cases hm : Mem.loadInt s.st.1.dmem (tp + 8#64) 8 with
    | some j => rw [exec_movfs_load_mapped hc ha hm] at hx; cases hx
    | none =>
      rw [exec_movfs_load_agrees hc ha hm (agrees_of_decls hdc _ _)] at hx
      injection hx with hx
      injection hx with _ _ hL
      injection hL with hA'
      exact (htp8 hA').elim
  -- the flag load `movq (%rcx), %rax`: lands at `q` with the value in `%rax`
  · have hc : CellAt s (ldDir .rcx 0 .rax) 3 := (code_field hp hend hld rfl s he hn).cell0 rfl rfl hpc
    have ha : eaddr s 3 (mB .rcx 0) = A := (eaddr_mB s 3 .rcx 0).trans (by rw [hA.regs, hJ.2]; simp)
    cases hm : Mem.loadInt s.st.1.dmem A 8 with
    | some j => rw [exec_load_mapped hc ha hm] at hx; cases hx
    | none =>
      rw [exec_load_agrees hc ha hm (agrees_of_decls hdc _ _)] at hx
      simp only [Option.some.injEq] at hx
      obtain ⟨-, -, -, rfl⟩ := hx
      refine fun v => ⟨_, rfl, ?_, ?_⟩
      · show s.st.2 + Int64.ofNat 3 = q
        rw [hpc, hq]; simp only [NX, Int64.add_assoc]; rfl
      · simp [Reg64s.set, Reg64s.set64]

/-- **`scc_rt_park`'s states are in `FlagW`** with the flag runs at return label `xl`
(`X64WakeMainF.parkGW_flag` with `hflag` at `flagRunsL xl`, which contains `scc_rt_park`'s runs): their
control is the loop's `c0`, their instructions no load of the flag's word (blocks, the `xchg`s, the `syscall`,
the thread pointer's load at `tp ≠ A`, `htp`), their pcs off `q`. -/
theorem parkGWX_flag {c0 : Ctl} {rbp0 ra tp : BitVec 64} (hR : R.OK) (hlo : R.lo ≤ -56) (hhi : 8 ≤ R.hi)
    (hcode : Spike.Lib.X64.Flow.Park.Code c0 rbp0 ra tp exe endPc)
    (hflag : RunsNe (_root_.Executable.labels exe).label q (flagRunsL xl))
    (h0 : Spike.Lib.X64WakeMainF.Flag0 lbl lsize c0 A) (htp : tp ≠ A) :
    Spike.Lib.X64.Flow.Park.ParkGW (fun s c => FlagW lbl lsize q s c) exe endPc R F c0 rbp0 ra tp := by
  refine {
    e := blkW_flag Park.b0_ok hR hlo hhi hcode.e h0 parkC (by ne_blk "scc_rt_park" 0 8 0 Park.b0)
    fsl := nodeW_flag h0 parkC (fun s ⟨he, hn, hdc, hpc, σ, hA, _, hJ⟩ kl k' hx => ?_)
      (by ne_one ".Lscc_rt_park.entry" 0 50 0)
    n1 := blkW_flag Park.b1_ok hR hlo hhi hcode.n1 h0 parkC (by ne_blk ".Lscc_rt_park.entry" 0 50 9 Park.b1)
    xchg1 := nodeW_flag h0 parkC
      (fun s ⟨he, hn, _, hpc, _⟩ _ _ hx => (xchg_noLoad ((hcode.xchg1 s he hn).cell0 rfl rfl hpc) hx).elim)
      (by ne_one ".Lscc_rt_park.entry" 0 50 24)
    n2 := blkW_flag Park.b2_ok hR hlo hhi hcode.n2 h0 parkC (by ne_blk ".Lscc_rt_park.entry" 0 50 28 Park.b2)
    n3 := blkW_flag Park.b3_ok hR hlo hhi hcode.n3 h0 parkC (by ne_blk ".Lscc_rt_park.entry" 0 50 48 Park.b3)
    wait := blkW_flag Park.b4_ok hR hlo hhi hcode.wait h0 parkC (by ne_blk ".Lscc_rt_park.wait" 0 92 0 Park.b4)
    sys := nodeW_flag h0 parkC
      (fun s ⟨he, hn, _, hpc, _⟩ _ _ hx => (syscall_noLoad ((hcode.sys s he hn).cell0 rfl rfl hpc) hx).elim)
      (by ne_one ".Lscc_rt_park.wait" 0 92 62)
    n5 := blkW_flag Park.b5_ok hR hlo hhi hcode.n5 h0 parkC (by ne_blk ".Lscc_rt_park.wait" 0 92 64 Park.b5)
    xchg2 := nodeW_flag h0 parkC
      (fun s ⟨he, hn, _, hpc, _⟩ _ _ hx => (xchg_noLoad ((hcode.xchg2 s he hn).cell0 rfl rfl hpc) hx).elim)
      (by ne_one ".Lscc_rt_park.wait" 0 92 79)
    n6 := blkW_flag Park.b6_ok hR hlo hhi hcode.n6 h0 parkC (by ne_blk ".Lscc_rt_park.wait" 0 92 83 Park.b6)
    done := blkW_flag Park.b7_ok hR hlo hhi hcode.done h0 parkC (by ne_blk ".Lscc_rt_park.done" 0 5 0 Park.b7) }
  -- the thread pointer's load `movq %fs:0, %rax`: `tp`, not the flag's word
  have hc : CellAt s (fsDir .rax 0) 9 := (hcode.fsl s he hn).cell0 rfl rfl hpc
  have ha : fsAddr s 9 { base := none, idx := none, disp := .int64 0 } = tp := by
    simp [fsAddr, eaddr, AddrExpr.interp, ConstExpr.interp, hA.regs, hJ.2.2.2]
  cases hm : Mem.loadInt s.st.1.dmem tp 8 with
  | some j => rw [exec_movfs_load_mapped hc ha hm] at hx; cases hx
  | none =>
    rw [exec_movfs_load_agrees hc ha hm (agrees_of_decls hdc _ _)] at hx
    injection hx with hx
    injection hx with _ _ hL
    injection hL with hA'
    exact (htp hA').elim

end Spike.Lib.X64HelloLoopWX

/-- info: 'Spike.Lib.X64HelloLoopWX.loopWX_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloLoopWX.loopWX_main

/-- info: 'Spike.Lib.X64HelloLoopWX.loopWX_relW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloLoopWX.loopWX_relW

/-- info: 'Spike.Lib.X64HelloLoopWX.loopWX_sys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloLoopWX.loopWX_sys

/-- info: 'Spike.Lib.X64HelloLoopWX.loopWX_flag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloLoopWX.loopWX_flag

/-- info: 'Spike.Lib.X64HelloLoopWX.parkGWX_flag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloLoopWX.parkGWX_flag
