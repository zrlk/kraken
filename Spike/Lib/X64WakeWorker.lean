/-
**wake.w's worker rows on x86-64** (the x64 twin of
`Spike/Lib/A64WakeWorker.lean`): the target side of `wake.w`'s `wc_worker`
(`store rel c 1`, `unpark j`, return; no print) and of
`scc_rt_thr_worker` (the call of `wc_worker`, the `exited` release, the
`exit`), over the thread rows (`OutT`, `SegT`). The listing is wake.w's
(`SccCode.wakeText`, `Spike/Lib/X64WakeCode.lean`).

- `WkTailW.seg_wkTailW`: `wc_worker` from `.Lwc_worker.entry` (after its
  stack-checked prologue, frame of 16: `c`/`j` at `-8(%rbp)`/`-16(%rbp)`,
  offsets `-16`/`-24`) to its return: the `movq` store (the source's store,
  `relStore_nd`), the call of `scc_rt_unpark` as a given node, the epilogue
  at `.Lwc_worker.x14`; `WkTailW.seg_unparkCallW` discharges the call with
  `Unpark.seg_unpark` (`WkTailW.seg_wkTailWU`, region `[-72, 8)`).
- `ThrTailW.seg_thrTailW`: `scc_rt_thr_worker`'s tail from
  `.Lscc_rt_thr_worker.x12` (frame of 32, the thread pointer spilled at
  `-24(%rbp)`).
- `ThrHeadW.seg_thrHeadW`: `scc_rt_thr_worker`'s `.entry` block (`%rdi`,
  `%rsi` from the frame, `call wc_worker`) and the call (`call_ndT`,
  `wc_worker`'s segment given in every region `[-72, 8)` from its entry
  `%rsp`, which is at `-48`: the region reaches `-120`).

**Unlike AArch64** (forced by the x64 shape):

- x64's local labels carry no numbered prefix (`.Lwc_worker.entry`, not
  `.L19_wc_worker.0_entry`), so `N` and `Code` take no `pfx`.
- byte offsets: `wc_worker`'s store is at `.entry + 11`, its `movq`/`call`
  block at `.entry + 14`, the return label `.x14` at `.entry + 23`;
  `scc_rt_thr_worker`'s tail is at `.x12` (the thread-pointer load), `+ 9`,
  `+ 24` (the `exited` store), `+ 28`, `+ 40` (the `syscall`).
- `%rbp` frames whose regions end at `8`; the `call` pushes the return
  address (`wc_worker`'s `.unpk` node at offset `-32`, the return address
  in cell `-32`), and the return lands at offsets that know `%rsp` alone
  (`⟨-24, []⟩`, `⟨-40, []⟩`), so the invariants carry `%rbp = sp - 8` for a
  ghost `sp` (the region's base, `R.addr 0`) and the epilogue's node claims
  `%rbp`'s offset back (`WaitLoop.At.rbpOf`), as in
  `Spike/Lib/X64WaitLoop.lean`. Nodes `.n3`/`.bl` of AArch64 are one node
  `.n3` here: `movq -16(%rbp), %rdi; call scc_rt_unpark` is one block of the
  listing.
- the thread pointer is `fsBase`, and `scc_rt_thr_worker`'s tail reads it
  from the TCB's self pointer `movq %fs:0, %rax` (AArch64: `mrs x9,
  tpidr_el0`, a register). As in `Park.seg_park` that load is
  `ownFsld_nd`: the word mapped for the load (`hT`, `LdOk`) and owned by
  the worker with value `tp` at `.x12` (`hown`, `OwnAt`).
- TSO: both stores are plain `movq`s (no `stlr`).
-/
import Spike.Lib.X64WorkerRows
import Spike.Lib.X64WaitLoop

namespace Spike.Lib.X64.Flow.Worker.Wake

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib.X64
open Scc.Sem (ValRep)
open Spike.Lib Spike.Lib.X64.Flow Spike.Lib.X64.Flow.Worker
open Spike.Lib.X64.Flow.Ret0 (StOk LdOk)

set_option linter.unusedSimpArgs false

/-! ## `wc_worker`

    .entry: %rcx = c (-8(%rbp)); %rax = 1
            movq %rax, (%rcx)               -- the source's `store rel c 1`
            %rdi = j (-16(%rbp))
            call scc_rt_unpark              -- the source's `unpark j` (inside)
    .x14:   epilogue; ret

The region is the frame, offsets `[-32, 8)` from the `%rsp` at entry (the
return address at `0`, the saved `%rbp` at `-8`, `c` at `-16`, `j` at
`-24`, the return address of the call at `-32`). Ghosts as in AArch64's
`WkTailW`: the source controls `c0` (at `let d = store rel a b in e1`),
`c1` (past the store), `c2` (past the `unpark`), the address `A` of `c` and
the tid `B` of `j` in their cells, the caller's `%rbp` `rbp0`, the return
address `ra`, the thread pointer `tp`; and the entry `%rsp` `sp`
(`%rbp = sp - 8`). -/

namespace WkTailW

def b0 : List (Directive × Nat) := (parse("movq -8(%rbp), %rcx
movq $1, %rax")).zip [4, 7]
def b1 : List (Directive × Nat) := (parse("movq -16(%rbp), %rdi
call scc_rt_unpark")).zip [4, 5]
def b2 : List (Directive × Nat) := (parse("movq %rbp, %rsp
popq %rbp
ret")).zip [3, 1, 1]

/-- The function's offsets inside the frame. -/
abbrev oI : SO := ⟨-24, [(.rbp, -8)]⟩
/-- The offsets after the call's return (`%rbp` from the invariant). -/
abbrev oP : SO := ⟨-24, []⟩
/-- The offsets at the callee's entry. -/
abbrev oS : SO := ⟨-32, [(.rbp, -8)]⟩
/-- The offsets after the return. -/
abbrev oR : SO := ⟨8, []⟩

block_spec b0 (-32) 8 oI b0
block_spec b1 (-32) 8 oI b1
block_spec b2 (-32) 8 oI b2

/-- The internal nodes. -/
inductive PN where
  | e | st | n3 | unpk | x14

/-- The exits. -/
inductive PX where
  | ret

section Spec

variable (lab : Label → Int64) (c0 c1 c2 : Ctl) (A B rbp0 ra tp sp : BitVec 64)

/-- Inside the frame, the source at `c'`: the caller's `%rbp`, the return
address, `A` and `B` in their cells, the thread pointer `tp`, `%rbp` at the
saved `%rbp`. -/
def JI (c' : Ctl) (σ : AS) (c : Ctl) : Prop :=
  c = c' ∧ σ.slot (-8) = rbp0 ∧ σ.slot 0 = ra ∧ σ.slot (-16) = A ∧ σ.slot (-24) = B ∧
    σ.regs.fsBase.toBitVec = tp ∧ σ.regs.rbp.toBitVec = sp - 8#64

/-- The return address of the call. -/
abbrev raU : BitVec 64 := (lab ".Lwc_worker.entry" + 14).toBitVec + 9#64

/-- **The nodes.** -/
def N : PN → ND
  | .e => ⟨lab ".Lwc_worker.entry", oI, JI A B rbp0 ra tp sp c0⟩
  | .st => ⟨lab ".Lwc_worker.entry" + 11, oI, fun σ c => JI A B rbp0 ra tp sp c0 σ c ∧
      σ.regs.get64 .rcx = A ∧ σ.regs.get64 .rax = 1#64⟩
  | .n3 => ⟨lab ".Lwc_worker.entry" + 14, oI, JI A B rbp0 ra tp sp c1⟩
  | .unpk => ⟨lab "scc_rt_unpark", oS, fun σ c => JI A B rbp0 ra tp sp c1 σ c ∧ σ.regs.get64 .rdi = B ∧
      σ.slot (-32) = raU lab⟩
  | .x14 => ⟨lab ".Lwc_worker.x14", oP, JI A B rbp0 ra tp sp c2⟩

/-- **The exit**: the return to `ra` with `%rsp` past the return address,
`%rbp` and the thread pointer as at entry, the source past its `unpark`. -/
def E : PX → ND
  | .ret => ⟨Int64.ofBitVec ra, oR, fun σ c => c = c2 ∧ σ.regs.get64 .rbp = rbp0 ∧
      σ.regs.fsBase.toBitVec = tp⟩

/-- **The code**: every block and the store at its node's pc. -/
structure Code (exe : _root_.Executable) (endPc : Int64) : Prop where
  e : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 c1 c2 A B rbp0 ra tp sp .e).pc b0
  st : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 c1 c2 A B rbp0 ra tp sp .st).pc [(stDir .rcx 0 .rax, 3)]
  n3 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 c1 c2 A B rbp0 ra tp sp .n3).pc b1
  x14 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 c1 c2 A B rbp0 ra tp sp .x14).pc b2

/-- The code does not depend on the ghosts (the nodes' pcs do not). -/
theorem Code.ghost {exe : _root_.Executable} {endPc : Int64} {c0 c1 c2 c0' c1' c2' : Ctl}
    {A B rbp0 ra tp sp A' B' rbp0' ra' tp' sp' : BitVec 64}
    (h : Code c0 c1 c2 A B rbp0 ra tp sp exe endPc) :
    Code c0' c1' c2' A' B' rbp0' ra' tp' sp' exe endPc :=
  ⟨h.e, h.st, h.n3, h.x14⟩

end Spec

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 c1 c2 : Ctl}
  {A B rbp0 ra tp sp : BitVec 64}

set_option hygiene false in
/-- A block node: the block, its `okBlk`, its code; the edge is left. -/
local macro "node " b:ident ok:ident f:ident : tactic =>
  `(tactic| refine (seg_nd (by simp [$b:ident]) $ok hF hR hlo hhi
    (fun s he hn => hcode.$f s he hn) fun σ c hJ => ⟨c, .refl c, ?_⟩).toT)

/-- Hitting node `j`. -/
local macro "hit " j:term : tactic =>
  `(tactic| (refine .inl ⟨$j, ?_, rfl, ?_⟩ <;>
    simp_all [N, JI, Int64.add_assoc, upd_apply, Reg64s.get64_set64_self,
      Reg64s.get64_set64_ne, KeepTP.set64_tp, Reg64s.set64, Reg64s.get64]))

/-- **`wc_worker` after its prologue is one segment with the thread rows**,
from `.entry` to its return: the `movq` to `c` is the source's `store rel c
1` (`Out.store`), the call of `scc_rt_unpark` the given node `hunpk`, the
rest stutters. The ghost `sp` is the region's base. -/
theorem seg_wkTailW (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -32) (hhi : 8 ≤ R.hi)
    (hdm : ∀ m, F m → Mem.loadInt m.dmem A 8 = none)
    {d : String} {a b : CoreTerm.At} {e1 : Expr} {ty tb : Ty} {w wb : TermRun.Word}
    (ht : c0.term = .let_ d (.store true a b none) e1) (hev : TermRun.evalAt c0.env a = some (ty, [w]))
    (hv : ValRep lbl w.val A.toNat) (htag : ∃ sa, w.val = .loc sa 0)
    (hevb : TermRun.evalAt c0.env b = some (tb, [wb])) (hvb : ValRep lbl wb.val 1)
    (hc1 : c1 = ⟨e1, (d, .unit, []) :: c0.env, none⟩)
    (hcode : Code c0 c1 c2 A B rbp0 ra tp (R.addr 0) exe endPc)
    (hunpk : SegT p lbl ms
      (At exe endPc R F (N (_root_.Executable.labels exe).label c0 c1 c2 A B rbp0 ra tp (R.addr 0) .unpk))
      (At exe endPc R F (N (_root_.Executable.labels exe).label c0 c1 c2 A B rbp0 ra tp (R.addr 0) .x14))) :
    SegT p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label c0 c1 c2 A B rbp0 ra tp (R.addr 0) .e))
      (fun s c => ∃ x, At exe endPc R F (E c2 rbp0 ra tp x) s c) := by
  refine fn_segT (N := N _ c0 c1 c2 A B rbp0 ra tp (R.addr 0)) (E := E c2 rbp0 ra tp) (fun i => ?_) PN.e
  cases i
  case e => node b0 b0_ok e; rw [N, b0_run]; hit PN.st
  case st =>
    refine (relStore_nd (A := A) (fun s he hn => hcode.st s he hn) hdm fun m σ c _ _ hJ => ?_).toT
    obtain ⟨⟨rfl, hJ⟩, hc, ha⟩ := hJ
    refine ⟨by rw [bAddr, hc]; simp, d, a, b, e1, ty, tb, w, wb, ht, hev, hv, htag, hevb,
      by rw [ha]; exact hvb, ?_⟩
    rw [← hc1]
    hit PN.n3
  case n3 => node b1 b1_ok n3; rw [N, b1_run]; hit PN.unpk
  case unpk => exact hunpk.mono_post fun s c h => .inl ⟨PN.x14, h⟩
  case x14 =>
    refine ((seg_nd (n := ⟨_, oI, _⟩) (by simp [b2]) b2_ok hF hR hlo hhi
      (fun s he hn => hcode.x14 s he hn) fun σ c hJ => ⟨c, .refl c, ?_⟩).mono_pre
      fun _ _ h => WaitLoop.At.rbpOf h fun σ c hJ => by
        show σ.regs.rbp.toBitVec = _; rw [hJ.2.2.2.2.2.2, WaitLoop.addr0_sub8]).toT
    rw [b2_run]
    refine .inr ⟨PX.ret, ?_, rfl, ?_⟩ <;>
      simp_all [N, E, JI, Int64.add_assoc, upd_apply, Reg64s.get64_set64_self, Reg64s.get64_set64_ne,
        KeepTP.set64_tp]

/-- **The call of `scc_rt_unpark`** (`call_ndT` with `Unpark.seg_unpark`,
region `[-40, 8)` from the call's `%rsp`, which is at offset `-32`): from
`.unpk` back to `.x14`, the frame unmoved, the source from `c1` (at its
`let x = unpark a in e`, `a`'s word representing `B`) to `c2` (past it).
The ghosts of `seg_unpark` are `%rbp` and the return address at the call.
The facts it needs are hypotheses: the kernel model (`hK`), the permit
word's (`hS`, `htp4`), the routine's code (`hpcode`, any ghosts:
`Unpark.Code.ghost`) and prologue fall-through (`hpentry`), and the return
label `.x14` after the `call` (`hx14`). -/
theorem seg_unparkCallW (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -72) (hhi : 8 ≤ R.hi)
    (hK : ms.K = some Scc.Sem.X64.abi)
    (hS : StOk ms F (B + 16#64) 1#64) (htp4 : (B + 16#64).toNat % 4 = 0)
    {x : String} {a : CoreTerm.At} {e : Expr} {ty : Ty} {jw : TermRun.Word}
    (ht : c1.term = .let_ x (.ext .unpark a) e) (hh : c1.hold = none)
    (hev : TermRun.evalAt c1.env a = some (ty, [jw])) (hv : ValRep lbl jw.val B.toNat)
    (hc2 : c2 = ⟨e, (x, ExtName.unpark.sig.2, []) :: c1.env, none⟩)
    {c0' c1' : Ctl} {B' rbp0' ra' tp' : BitVec 64} (hpcode : Unpark.Code c0' c1' B' rbp0' ra' tp' exe endPc)
    (hpentry : (_root_.Executable.labels exe).label ".Lscc_rt_unpark.entry" =
      (_root_.Executable.labels exe).label "scc_rt_unpark" + 12)
    (hx14 : (_root_.Executable.labels exe).label ".Lwc_worker.x14" =
      (_root_.Executable.labels exe).label ".Lwc_worker.entry" + 14 + 9) :
    SegT p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label c0 c1 c2 A B rbp0 ra tp sp .unpk))
      (At exe endPc R F (N (_root_.Executable.labels exe).label c0 c1 c2 A B rbp0 ra tp sp .x14)) := by
  refine (call_ndT (e0 := 0) (lo' := -40) (hi' := 8)
    (N := fun _ : Unit => N (_root_.Executable.labels exe).label c0 c1 c2 A B rbp0 ra tp sp .x14)
    (E := fun e : Empty => e.elim)
    (Ne := fun g : BitVec 64 × BitVec 64 =>
      Unpark.N (_root_.Executable.labels exe).label c1 c2 B g.1 g.2 tp .e)
    (Ex := fun g y => Unpark.E c2 g.1 g.2 tp y)
    hR hF (by show R.lo ≤ -32 - 0 + -40; omega) (by decide) (by show (-32 : Int) - 0 < R.hi; omega)
    (by show (-32 : Int) - 0 + 8 ≤ R.hi; omega) (by show ((-32 : Int) - 0) % 8 = 0; decide) (by decide)
    (by decide)
    (fun R' F' hR' hlo' hhi' hF' hFF g =>
      Unpark.seg_unpark hF' hR' hlo' hhi' hK (hS.mono hFF) htp4 ht hh hev hv hc2 hpcode.ghost hpentry)
    (fun _ => rfl) ?_ ?_).mono_post fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim
  · rintro σC c ⟨⟨rfl, -, -, -, -, htp, -⟩, hdi, -⟩
    exact ⟨(σC.regs.rbp.toBitVec, σC.slot (-32 - 0 + 0)), rfl, rfl, hdi, rfl, rfl, htp⟩
  · rintro ⟨rbp1, ra1⟩ ⟨⟩ σC c σx c' σR ⟨⟨rfl, h8, h0, h16, h24, -, hbp⟩, -, h32⟩ ⟨hc, -, hrb, hra, -⟩
      ⟨hc', hrb', htp'⟩ hreg - - hslot
    have hout : ∀ k : Int, -24 ≤ k → k % 8 = 0 → k ≤ 0 → σR.slot k = σC.slot k := fun k h1 h2 h3 =>
      hslot k ⟨h2, by omega, by omega⟩ fun ⟨_, _, h⟩ => by
        simp only [Region.callee, N] at h; omega
    refine .inl ⟨(), ?_, by show SO.le oP ⟨-32 - 0 + 8, []⟩ = true; decide, hc',
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · subst hra
      show (_root_.Executable.labels exe).label ".Lwc_worker.x14" = Int64.ofBitVec (σC.slot (-32))
      rw [h32, hx14]; rfl
    · rw [hout (-8) (by decide) (by decide) (by decide)]; exact h8
    · rw [hout 0 (by decide) (by decide) (by decide)]; exact h0
    · rw [hout (-16) (by decide) (by decide) (by decide)]; exact h16
    · rw [hout (-24) (by decide) (by decide) (by decide)]; exact h24
    · show σR.regs.fsBase.toBitVec = tp
      rw [hreg]; exact htp'
    · show σR.regs.rbp.toBitVec = _
      have : σx.regs.get64 .rbp = rbp1 := hrb'
      rw [hreg]; simp only [Reg64s.get64] at this; rw [this]
      exact (show σC.regs.rbp.toBitVec = rbp1 from hrb).symm.trans hbp

/-- **`wc_worker` after its prologue, its `unpark` call discharged**
(`seg_wkTailW` with `hunpk` from `seg_unparkCallW`): the region holds
`scc_rt_unpark`'s frame below the worker's (`hlo`, `-72`). -/
theorem seg_wkTailWU (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -72) (hhi : 8 ≤ R.hi)
    (hdm : ∀ m, F m → Mem.loadInt m.dmem A 8 = none)
    {d : String} {a b : CoreTerm.At} {e1 : Expr} {ty tb : Ty} {w wb : TermRun.Word}
    (ht : c0.term = .let_ d (.store true a b none) e1) (hev : TermRun.evalAt c0.env a = some (ty, [w]))
    (hv : ValRep lbl w.val A.toNat) (htag : ∃ sa, w.val = .loc sa 0)
    (hevb : TermRun.evalAt c0.env b = some (tb, [wb])) (hvb : ValRep lbl wb.val 1)
    (hc1 : c1 = ⟨e1, (d, .unit, []) :: c0.env, none⟩)
    (hcode : Code c0 c1 c2 A B rbp0 ra tp (R.addr 0) exe endPc)
    (hK : ms.K = some Scc.Sem.X64.abi)
    (hS : StOk ms F (B + 16#64) 1#64) (htp4 : (B + 16#64).toNat % 4 = 0)
    {x : String} {au : CoreTerm.At} {e : Expr} {tu : Ty} {jw : TermRun.Word}
    (htu : c1.term = .let_ x (.ext .unpark au) e) (hhu : c1.hold = none)
    (hevu : TermRun.evalAt c1.env au = some (tu, [jw])) (hvu : ValRep lbl jw.val B.toNat)
    (hc2 : c2 = ⟨e, (x, ExtName.unpark.sig.2, []) :: c1.env, none⟩)
    {c0' c1' : Ctl} {B' rbp0' ra' tp' : BitVec 64} (hpcode : Unpark.Code c0' c1' B' rbp0' ra' tp' exe endPc)
    (hpentry : (_root_.Executable.labels exe).label ".Lscc_rt_unpark.entry" =
      (_root_.Executable.labels exe).label "scc_rt_unpark" + 12)
    (hx14 : (_root_.Executable.labels exe).label ".Lwc_worker.x14" =
      (_root_.Executable.labels exe).label ".Lwc_worker.entry" + 14 + 9) :
    SegT p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label c0 c1 c2 A B rbp0 ra tp (R.addr 0) .e))
      (fun s c => ∃ x, At exe endPc R F (E c2 rbp0 ra tp x) s c) :=
  seg_wkTailW hF hR (Int.le_trans hlo (by decide)) hhi hdm ht hev hv htag hevb hvb hc1 hcode
    (seg_unparkCallW hF hR hlo hhi hK hS htp4 htu hhu hevu hvu hc2 hpcode hpentry hx14)

end Proof

/-- info: 'Spike.Lib.X64.Flow.Worker.Wake.WkTailW.seg_wkTailWU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms seg_wkTailWU

end WkTailW

/-! ## `scc_rt_thr_worker`'s tail

    .x12:  %rax = %fs:0 (the TCB's self pointer: tp); spilled at -24(%rbp)
           %rcx = tp; %rax = 1
           movq %rax, 24(%rcx)            -- the thread's `exited` word
           %rdi = 0; %eax = 60
           syscall                        -- exit: the thread ends
           (dead: movq %rax, -32(%rbp); ud2)

The region is the frame, offsets `[-40, 8)`. Ghosts: the source control
`c0` (the worker returned: at `ret a`), the thread pointer `tp`, the entry
`%rsp` `sp` (`%rbp = sp - 8`). `.x12` is entered by `wc_worker`'s return,
at offsets that know `%rsp` alone. -/

namespace ThrTailW

def b0 : List (Directive × Nat) := (parse("movq %rax, -24(%rbp)
movq -24(%rbp), %rcx
movq $1, %rax")).zip [4, 4, 7]
def b1 : List (Directive × Nat) := (parse("movq $0, %rdi
movl $60, %eax")).zip [7, 5]

/-- The function's offsets inside the frame. -/
abbrev oI : SO := ⟨-40, [(.rbp, -8)]⟩
/-- The offsets after `wc_worker`'s return (`%rbp` from the invariant). -/
abbrev oP : SO := ⟨-40, []⟩

block_spec b0 (-40) 8 oI b0
block_spec b1 (-40) 8 oI b1

/-- The internal nodes. -/
inductive PN where
  | x12 | n1 | ex | n2 | sys

section Spec

variable (lab : Label → Int64) (c0 : Ctl) (tp sp : BitVec 64)

/-- **The nodes.** -/
def N : PN → ND
  | .x12 => ⟨lab ".Lscc_rt_thr_worker.x12", oP, fun σ c => c = c0 ∧ σ.regs.fsBase.toBitVec = tp ∧
      σ.regs.rbp.toBitVec = sp - 8#64⟩
  | .n1 => ⟨lab ".Lscc_rt_thr_worker.x12" + 9, oP, fun σ c => c = c0 ∧ σ.regs.get64 .rax = tp ∧
      σ.regs.rbp.toBitVec = sp - 8#64⟩
  | .ex => ⟨lab ".Lscc_rt_thr_worker.x12" + 24, oI, fun σ c => c = c0 ∧ σ.regs.get64 .rcx = tp ∧
      σ.regs.get64 .rax = 1#64⟩
  | .n2 => ⟨lab ".Lscc_rt_thr_worker.x12" + 28, oI, fun _ c => c = c0⟩
  | .sys => ⟨lab ".Lscc_rt_thr_worker.x12" + 40, oI, fun σ c => c = c0 ∧ σ.regs.get64 .rax = 60#64⟩

/-- **The code**: every block and single instruction at its node's pc. -/
structure Code (exe : _root_.Executable) (endPc : Int64) : Prop where
  x12 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 tp sp .x12).pc [(fsDir .rax 0, 9)]
  n1 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 tp sp .n1).pc b0
  ex : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 tp sp .ex).pc [(stDir .rcx 24 .rax, 4)]
  n2 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 tp sp .n2).pc b1
  sys : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 tp sp .sys).pc [(op64 .syscall, 2)]

/-- The code does not depend on the ghosts. -/
theorem Code.ghost {exe : _root_.Executable} {endPc : Int64} {c0 c0' : Ctl} {tp sp tp' sp' : BitVec 64}
    (h : Code c0 tp sp exe endPc) : Code c0' tp' sp' exe endPc :=
  ⟨h.x12, h.n1, h.ex, h.n2, h.sys⟩

end Spec

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl} {tp : BitVec 64}

set_option hygiene false in
/-- A block node: the block, its `okBlk`, its code; the edge is left. -/
local macro "node " b:ident ok:ident f:ident : tactic =>
  `(tactic| refine (seg_nd (by simp [$b:ident]) $ok hF hR hlo hhi
    (fun s he hn => hcode.$f s he hn) fun σ c hJ => ⟨c, .refl c, ?_⟩).toT)

/-- Hitting node `j`. -/
local macro "hit " j:term : tactic =>
  `(tactic| (refine .inl ⟨$j, ?_, rfl, ?_⟩ <;>
    simp_all [N, Int64.add_assoc, upd_apply, Reg64s.get64_set64_self,
      Reg64s.get64_set64_ne, KeepTP.set64_tp, fsStep, Reg64s.set64, Reg64s.get64]))

/-- **`scc_rt_thr_worker`'s tail is one segment with the thread rows** from
`.x12` to any fragment: the thread pointer read from the TCB's self pointer
(owned by the worker with value `tp` there: `hown`, mapped for the load:
`hT`), the release of the thread's `exited` word (at `tp + 24`, `StOk`),
then the `exit` with the source at `ret a` (`OutT.texit`); the source
stutters until then. The ghost `sp` is the region's base. -/
theorem seg_thrTailW {Q : Frag isa} (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -40) (hhi : 8 ≤ R.hi)
    (hK : ms.K = some Scc.Sem.X64.abi) (hT : LdOk ms F tp)
    (hown : OwnAt ms exe endPc ((_root_.Executable.labels exe).label ".Lscc_rt_thr_worker.x12") tp tp)
    (hS : StOk ms F (tp + 24#64) 1#64) {a : CoreTerm.At} (ht : c0.term = .ret a)
    (hcode : Code c0 tp (R.addr 0) exe endPc) :
    SegT p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label c0 tp (R.addr 0) .x12)) Q := by
  refine (fn_segT (N := N _ c0 tp (R.addr 0)) (E := (nofun : Empty → ND)) (fun i => ?_) PN.x12).mono_post
    fun _ _ ⟨x, _⟩ => x.elim
  cases i
  case x12 =>
    refine (ownFsld_nd (by decide) hF (fun s he hn => hcode.x12 s he hn) hown fun m σ c _ hm hJ => ?_).toT
    obtain ⟨hc0, hfs, hbp⟩ := hJ
    have ha : σ.regs.fsBase.toBitVec + (0 : Int64).toBitVec = tp := by rw [hfs]; exact BitVec.add_zero tp
    refine ⟨ha, hT.rt, hT.mp, hT.unmapped m hm, c, .refl c, ?_⟩
    hit PN.n1
  case n1 =>
    refine ((seg_nd (n := ⟨_, oI, _⟩) (by simp [b0]) b0_ok hF hR hlo hhi
      (fun s he hn => hcode.n1 s he hn) fun σ c hJ => ⟨c, .refl c, ?_⟩).mono_pre
      fun _ _ h => WaitLoop.At.rbpOf h fun σ c hJ => by
        show σ.regs.rbp.toBitVec = _; rw [hJ.2.2, WaitLoop.addr0_sub8]).toT
    rw [b0_run]; hit PN.ex
  case ex =>
    refine (rtst_nd (fun s he hn => hcode.ex s he hn) fun m σ c _ hm hJ => ?_).toT
    obtain ⟨rfl, hc, ha⟩ := hJ
    have hA : bAddr σ.regs .rcx 24 = tp + 24#64 := by rw [bAddr, hc]; rfl
    rw [hA, ha]
    exact ⟨hS.rt, hS.mp, hS.G, hS.unmapped m hm, c, .refl c, by hit PN.n2⟩
  case n2 => node b1 b1_ok n2; rw [N, b1_run]; hit PN.sys
  case sys =>
    refine texit_nd hK (fun s he hn => hcode.sys s he hn) fun σ c ⟨hc, h60⟩ => ⟨?_, a, by rw [hc]; exact ht⟩
    have := congrArg BitVec.toNat h60; simpa [Reg64s.get64] using this

end Proof

/-- info: 'Spike.Lib.X64.Flow.Worker.Wake.ThrTailW.seg_thrTailW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms seg_thrTailW

end ThrTailW

/-! ## `scc_rt_thr_worker`'s head

    .entry: %rdi, %rsi = the words at -8(%rbp), -16(%rbp); call wc_worker
    .x12:   (ThrTailW)

The frame is `[-40, 8)`; `wc_worker` is entered at offset `-48` and runs
in its own region `[-72, 8)` from there (its frame, the unpark call's
return address and `scc_rt_unpark`'s frame), so the region reaches
`-120` (`Spike/Lib/X64WakeFrame.lean`'s `thrD`). -/

namespace ThrHeadW

/-- `scc_rt_thr_worker`'s `.entry` block: the arguments, the call. -/
def thE : List (Directive × Nat) := (parse("movq -8(%rbp), %rdi
movq -16(%rbp), %rsi
call wc_worker")).zip [4, 4, 5]

/-- The frame's offsets. -/
abbrev oI : SO := ⟨-40, [(.rbp, -8)]⟩

block_spec thE (-120) 8 oI thE

/-- The head's internal nodes. -/
inductive TN where
  | e | call

/-- **The head's nodes**, from the invariant `J` at `.entry`; across the
block the source moves from `c0` to `c` with `L c0 c` (a local run: the
worker's `split` of its argument pair). -/
def tN (lab : Label → Int64) (J : AS → Ctl → Prop) (L : Ctl → Ctl → Prop) : TN → ND
  | .e => ⟨lab ".Lscc_rt_thr_worker.entry", oI, J⟩
  | .call => ⟨lab "wc_worker", ⟨-48, [(.rbp, -8)]⟩, fun σ c => ∃ σ0 c0, J σ0 c0 ∧ L c0 c ∧
      σ = (arun lab thE ⟨lab ".Lscc_rt_thr_worker.entry", oI, σ0⟩).σ⟩

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **`scc_rt_thr_worker`'s head is one segment with the thread rows**,
from `.entry` (invariant `J`) to the caller's nodes `N`/exits `E`: the
block, then the call of `wc_worker` (`call_ndT`, `wc_worker`'s region
`[-72, 8)` from its entry `%rsp` at `-48`). `wc_worker`'s segment from its
entry `Ne g` to its exits `Ex g` is given for every region holding its
frames and every frame condition giving `F` (`hwk`); `hent` picks the
ghost at the call, `hret` lands its exits (the return to `.x12` is
`ThrTailW.N .x12`). The source takes a local run `L` across the block
(`hL`). -/
theorem seg_thrHeadW {ι κ : Sort _} {N : ι → ND} {E : κ → ND} (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -120) (hhi : 8 ≤ R.hi) {J : AS → Ctl → Prop}
    {L : Ctl → Ctl → Prop} (hL : ∀ σ c, J σ c → ∃ c', LocalRun p c c' ∧ L c c')
    (hcodeE : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s ((_root_.Executable.labels exe).label ".Lscc_rt_thr_worker.entry") thE)
    {γ : Type _} {κ' : Sort _} {Ne : γ → ND} {Ex : γ → κ' → ND}
    (hwk : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.lo ≤ -72 → 8 ≤ R'.hi →
      FStable R' F' → (∀ m, F' m → F m) → ∀ g,
        SegT p lbl ms (At exe endPc R' F' (Ne g)) (fun s c => ∃ x, At exe endPc R' F' (Ex g x) s c))
    (hNe : ∀ g, (Ne g).o = ⟨0, []⟩)
    (hent : ∀ σC c, (tN (_root_.Executable.labels exe).label J L .call).J σC c →
      ∃ g, (Ne g).pc = (_root_.Executable.labels exe).label "wc_worker" ∧ (Ne g).J (enter (-48 - 0) σC) c)
    (hret : ∀ g x σC c σx c' (σR : AS), (tN (_root_.Executable.labels exe).label J L .call).J σC c →
      (Ne g).J (enter (-48 - 0) σC) c → (Ex g x).J σx c' →
      σR.regs = σx.regs → σR.zmms = σx.zmms → σR.status = σx.status →
      (∀ k, R.Off k → ¬ (R.callee (-48 - 0) (-72) 8).Off (k - (-48 - 0)) → σR.slot k = σC.slot k) →
      Lands N E ⟨(Ex g x).pc, ⟨-48 - 0 + (Ex g x).o.sp, []⟩, σR⟩ c') :
    SegT p lbl ms (At exe endPc R F (tN (_root_.Executable.labels exe).label J L .e))
      (Next exe endPc R F N E) := by
  let lab := (_root_.Executable.labels exe).label
  refine SegT.seq (Q := At exe endPc R F (tN lab J L .call))
    (Seg.toT (seg_nd (N := fun _ : Unit => tN lab J L .call) (E := (nofun : Empty → ND)) (by simp [thE]) thE_ok
      hF hR hlo hhi hcodeE fun σ c hJ => ?_) |>.mono_post ?_) ?_
  · obtain ⟨c', hr, hl⟩ := hL σ c hJ
    refine ⟨c', hr, .inl ⟨(), ?_, ?_, σ, c, hJ, hl, rfl⟩⟩
    · simp only [tN]; rw [thE_run]
    · simp only [tN]; rw [thE_run]; rfl
  · rintro s c (⟨_, h⟩ | ⟨y, _⟩)
    · exact h
    · exact y.elim
  · exact call_ndT (e0 := 0) (lo' := -72) (hi' := 8) hR hF (by show R.lo ≤ -48 - 0 + -72; omega) (by decide)
      (by show (-48 : Int) - 0 < R.hi; omega) (by show (-48 : Int) - 0 + 8 ≤ R.hi; omega)
      (by show ((-48 : Int) - 0) % 8 = 0; decide) (by decide) (by decide) hwk hNe hent hret

end Proof

/-- info: 'Spike.Lib.X64.Flow.Worker.Wake.ThrHeadW.seg_thrHeadW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms seg_thrHeadW

end ThrHeadW

end Spike.Lib.X64.Flow.Worker.Wake
