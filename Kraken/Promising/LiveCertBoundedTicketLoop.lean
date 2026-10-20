/-
**Bounded certification for the repeated-acquire
AArch64 ticket lock** (`tkLoopWorker`, `ticketlock_loop2.kl`, valid layout):
`CertBoundedFrom Arch.armv8 c0 (12 * k + 2)` for every
`TicketLoop.TkLoopStart k …` configuration (`k` rounds per worker), and the
fuel-free liveness and termination theorems `ticket_loop_live_semU`
(`_concrete`) and `ticket_loop_term_semU`.

**The bound depends on the program only.** `F k = 12 * k + 2` is linear in the
round count `k`. `k` is a constant of the program text (`X7` at the start)
and a parameter of the theorems. `F` does not depend on the fuel, the thread
count or the layout.

**Route: the iteration cut** (`LiveCertCut`, used unchanged). A certifying
solo run of a worker may pass through all the rounds it has left, since an
outstanding promise of a later round's `next`, counter or `owner` write is
fulfilled only there. Outside the spin loop `LDAR; CMP; B.NE` (positions
6–8) every instruction moves forward (`TicketLoopPF.nextPc`). The rounds are
bounded by `X7`, which only the `SUB` changes (lowering it by one). The
reachable invariant gives `X7 ≤ k` (`TI.k7`) and `X7 ≠ 0` at positions
4–14 (`TI.x7`).

**The cut inside a spin visit.** A visit of the spin loop performs no write:
memory and promises stay the same, scalar views grow (`stepOne_grow`), and
only `X4`, the flags and their register views (slots 4 and 32) change
(`SpRel`). For two `LDAR` steps of the same visit, the later `LDAR` and the
`CMP` after it replay from the earlier `LDAR` state:

- the read replays below (`readSuccs_dom`);
- `CMP`'s flags are a function of the registers (`exec_cmp_pair`), so both
  runs reach the same machine state;
- the read's post-view and the flags' register view are dominated.

So the thread after the replay dominates (`Thread.Dom`) the thread after the
later `CMP`, and the loop between the two `LDAR`s is cut (`cut_6`,
`ThreadNPn.dom`). Two steps are replayed because the states at the two
`LDAR`s differ in the dead `X4` and flags, whose register views need not be
ordered.

**The potential** `Φ pos (wn X7) h`, where `h` means "an earlier `LDAR` of
this spin visit is recorded". A round from `round:` costs at most 12
instructions with no cut (`CBZ`, `LDADDA`, one `LDAR; CMP; B.NE`, then 7
more instructions to `B round`). The final `CBZ` costs 1. Every step lowers
`Φ` by at least one (`Φ_step`), except a second `LDAR` of a visit: that one
either ends the run or is followed by the `CMP` that completes a cut.
`Φ ≤ 12 * wn X7 + 2` (`Φ_le`), so certifications fit in `12 * k + 2`
instructions (`certOkN_bound`).

Names: `deps_6`, `deps_7`, `exec_cmp_pair`, `SpRel` (on `CertCut.RegS 4 32`),
`PI`, `step_6`, `step_7`, `spRel_step`, `cut_6`, `newFlag`, `Φ`, `Φ_step`,
`Φ_le`, `run_bound`, `certOkN_bound`, `XclbNone`, `ticket_loop_certBounded`,
`TicketLoopLiveSemU`, `TicketLoopTermSemU`, `ticket_loop_live_semU`,
`ticket_loop_live_semU_concrete`, `ticket_loop_term_semU`.
-/
import Kraken.Promising.LiveCertBounded
import Kraken.Promising.LiveCertCut
import Kraken.Promising.LiveCertCutRegS
import Kraken.Promising.LiveCertBoundedSpinCas
import Kraken.Promising.LiveTicketLoopSem

namespace Kraken.Promising.Live.CertBoundedTicketLoop

set_option linter.unusedSectionVars false

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live Kraken.Promising.Live.Sem
open Kraken.Promising.Live.TicketLoop Kraken.Promising.Live.TicketLoopTrees Kraken.Promising.Live.TicketLoopStatic
open Kraken.Promising.Live.TicketLoopInv Kraken.Promising.Live.TicketLoopCert Kraken.Promising.Live.TicketLoopInvP
open Kraken.Promising.Live.TicketStep Kraken.Promising.Live.SpinStep
open Kraken.Promising.Live.TicketInv (wn L4)
open Kraken.Promising.Live.TicketTrees (w32)
open Kraken.Promising.SLR.A64Trees (At goto next_pc)
open Kraken.Promising.Live.CertBounded Kraken.Promising.Live.CertCut
open Kraken.Promising.Live.TicketLoopPF (nextPc nextPc_mem pos_step_st tkLoopLayout tkLoopValid)

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout tkLoopWorker)]

set_option hygiene false in
local notation "pcA" => (layout tkLoopWorker).addrOf

/-! ## The spin cells: dependencies and the flags of `CMP` -/

/-- Read the dependencies of the cell at position `i` (as
`CertBoundedSpinCas`'s `a64deps`). -/
local macro "a64deps" h:ident i:num : tactic => `(tactic| (
  have hc := Kraken.Executable.codeAt_addrOf (p := tkLoopWorker) (i := $i) (d := tkLoopWorker[$i])
    (by decide) (by decide)
  rw [← ($h).pc] at hc
  generalize hd : tkLoopWorker[$i] = d at hc
  simp only [tkLoopWorker, List.getElem_cons_succ, List.getElem_cons_zero] at hd
  subst hd
  have hdir := CertBoundedSpinCas.directive_of_codeAt (by rw [($h).exe]; exact hc)
  show AArch64.deps _ = _
  unfold AArch64.deps
  rw [hdir]
  rfl))

/-- Read the cell at position `i` (`LiveTicketLoopTrees`'s `cell`). -/
local macro "cell" h:ident i:num "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  a64cell $h $i tkLoopWorker [tkLoopWorker] [label_round, label_spin, label_done] [goto, $ts,*])

/-- `ldar w4,[x1]`: address `X1`, load into `X4`. -/
theorem deps_6 (st : State) (h : At tkLoopWorker st 6) :
    isa.deps st = { addrRegs := [.x 1], loadDefs := [.x 4] } := by a64deps h 6

/-- `cmp w4,w3`: data `X4`, `X3`, defines the flags. -/
theorem deps_7 (st : State) (h : At tkLoopWorker st 7) :
    isa.deps st = { dataRegs := [.x 4, .x 3], defs := [.nzcv] } := by a64deps h 7

/-- **`CMP`'s flags are a function of the registers**: two states at
position 7 with the same registers get the same flags. -/
theorem exec_cmp_pair (st st' : State) (h : At tkLoopWorker st 7) (h' : At tkLoopWorker st' 7)
    (hr : st'.st.1.regs = st.st.1.regs) :
    ∃ s : StatusFlags, isa.exec st = some (.done (goto st { st.st.1 with status := s } (pcA 8))) ∧
      isa.exec st' = some (.done (goto st' { st'.st.1 with status := s } (pcA 8))) := by
  refine ⟨?s, ?e1, ?e2⟩
  case e1 =>
    rw [next_pc h (by decide)]
    cell h 7 []
    rfl
  case e2 =>
    rw [next_pc h' (by decide)]
    cell h' 7 []
    rw [hr]

omit hv in
theorem instrViews_6 (t : Thread isa) :
    instrViews t { addrRegs := [.x 1], loadDefs := [.x 4] } =
      { addrR := max 0 (t.rview[1]! : View), addrW := max 0 (t.wview[1]! : View), dataR := 0, dataW := 0,
        condW := 0 } := rfl

omit hv in
theorem instrViews_7 (t : Thread isa) :
    instrViews t { dataRegs := [.x 4, .x 3], defs := [.nzcv] } =
      { addrR := 0, addrW := 0, dataR := max (max 0 (t.rview[4]! : View)) t.rview[3]!,
        dataW := max (max 0 (t.wview[4]! : View)) t.wview[3]!, condW := 0 } := rfl

/-! ## The solo invariant and the spin relation -/

omit layout hv in
theorem setXReg_X4_X4 (r : Reg64s) (a b : BitVec 64) : (r.setXReg .X4 a).setXReg .X4 b = r.setXReg .X4 b := by
  simp [Reg64s.setXReg]

omit layout hv in
theorem setXReg_X4_self (r : Reg64s) : r.setXReg .X4 r.X4.toBitVec = r := by
  simp [Reg64s.setXReg]

/-- `b.ne spin`: a branch on the flags. -/
theorem deps_8 (st : State) (h : At tkLoopWorker st 8) :
    isa.deps st = { condRegs := [.nzcv], isBranch := true } := by a64deps h 8

variable {x o c : BitVec 64} {tid : Nat}

/-- **The solo invariant** of a worker: `SInv`, a round left wherever the
worker holds or takes a ticket, and no pending load exclusive. -/
structure PI (x o c : BitVec 64) (t : Thread isa) : Prop where
  sinv : SInv x o c t.st
  x7 : ∀ i ∈ [4, 6, 7, 8, 9, 10, 11, 12, 13, 14], t.st.st.2 = pcA i → wn t.st.st.1.regs.X7 ≠ 0
  xclb : t.views.xclb = none

/-- No cell of the worker performs a load exclusive. -/
theorem noXcl {t : Thread isa} (hS : SInv x o c t.st) : ∀ tree, isa.exec t.st = some tree → tree.NoXclLoad := by
  intro tree hex
  obtain ⟨hSt, p, hp, hpc⟩ := hS
  simp only [tkLoopPcs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [exec_mov _ (hSt.at (by decide) (by decide) hpc)] at hex; cases hex; trivial
  · rw [exec_cbz _ (hSt.at (by decide) (by decide) hpc)] at hex; cases hex; trivial
  · rw [exec_ldadda _ (hSt.at (by decide) (by decide) hpc) hSt.x0 hSt.dx] at hex; cases hex; exact fun _ => trivial
  · rw [exec_ldar _ (hSt.at (by decide) (by decide) hpc) hSt.x1 hSt.dO] at hex; cases hex
    exact ⟨rfl, fun _ => trivial⟩
  · obtain ⟨sf, h1, -⟩ := exec_cmp _ (hSt.at (by decide) (by decide) hpc)
    rw [h1] at hex; cases hex; trivial
  · rw [exec_bne _ (hSt.at (by decide) (by decide) hpc)] at hex; cases hex; trivial
  · rw [exec_ldr_c _ (hSt.at (by decide) (by decide) hpc) hSt.x2 hSt.dc] at hex; cases hex
    exact ⟨rfl, fun _ => trivial⟩
  · rw [exec_add5 _ (hSt.at (by decide) (by decide) hpc)] at hex; cases hex; trivial
  · rw [exec_str_c _ (hSt.at (by decide) (by decide) hpc) hSt.x2 hSt.dc] at hex; cases hex; exact fun _ => trivial
  · rw [exec_add4 _ (hSt.at (by decide) (by decide) hpc)] at hex; cases hex; trivial
  · rw [exec_stlr _ (hSt.at (by decide) (by decide) hpc) hSt.x1 hSt.dO] at hex; cases hex; exact fun _ => trivial
  · rw [exec_sub _ (hSt.at (by decide) (by decide) hpc)] at hex; cases hex; trivial
  · rw [exec_b_round _ (hSt.at (by decide) (by decide) hpc)] at hex; cases hex; trivial
  · have := stepOne_end hSt hpc Arch.armv8 0 default
    simp [stepOne, hex] at this

omit layout hv in
/-- Where the next position needs a round left, the current one had one. -/
theorem x7_next : ∀ i ∈ tkLoopPcs, ∀ z w : Bool, nextPc z w i ∈ [4, 6, 7, 8, 9, 10, 11, 12, 13, 14] →
    i ≠ 14 ∧ (i ∈ [4, 6, 7, 8, 9, 10, 11, 12, 13, 14] ∨ (i = 3 ∧ w = false)) := by decide

/-- **One instruction keeps the solo invariant**, with the next position,
and `X7` kept except at the `SUB`. -/
theorem pi_step {t : Thread isa} {mem : Memory} {outs : List (Except String (Outcome isa))} {oc : Outcome isa}
    (hP : PI x o c t) (hs : stepOne Arch.armv8 t tid mem = some outs) (ho : .ok oc ∈ outs) {i : Nat}
    (hi : i ∈ tkLoopPcs) (hpc : t.st.st.2 = pcA i) :
    PI x o c oc.thread ∧
      oc.thread.st.st.2 = pcA (nextPc t.st.st.1.status.z (decide (wn t.st.st.1.regs.X7 = 0)) i) ∧
      (i ≠ 14 → wn oc.thread.st.st.1.regs.X7 = wn t.st.st.1.regs.X7) ∧
      (i = 14 → wn oc.thread.st.st.1.regs.X7 + 1 = wn t.st.st.1.regs.X7) := by
  have h14 : i = 14 → wn t.st.st.1.regs.X7 ≠ 0 := fun e => hP.x7 14 (by decide) (e ▸ hpc)
  obtain ⟨hn, -, h7, h7'⟩ := pos_step_st hP.sinv.st hi hpc h14 hs ho
  obtain ⟨tree, -, -, hex, -⟩ := stepOne_fi Arch.armv8 hs ho
  refine ⟨⟨(step_sinv hP.sinv hs ho).1, fun j hj hjpc => ?_,
    stepOne_xclb_none Arch.armv8 hex (noXcl hP.sinv tree hex) hs ho hP.xclb⟩, hn,
    fun h => by rw [h7 h], h7'⟩
  have hnm := nextPc_mem t.st.st.1.status.z (decide (wn t.st.st.1.regs.X7 = 0)) i hi
  have e : j = nextPc t.st.st.1.status.z (decide (wn t.st.st.1.regs.X7 = 0)) i :=
    addrOf_inj (by simp only [tkLoopPcs, List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega) hnm
      (hjpc.symm.trans hn)
  subst e
  obtain ⟨hne, hcase⟩ := x7_next i hi _ _ hj
  rw [h7 hne]
  rcases hcase with hi' | ⟨rfl, hw⟩
  · exact hP.x7 i hi' hpc
  · simpa using hw

/-- **The spin relation**: `t` is `q` with `X4`, the flags, their register
views (slots 4 and 32) and the pc changed, scalar views grown, the same
forwarding table and promises, and no pending load exclusive. -/
structure SpRel (q t : Thread isa) : Prop where
  core : ∃ (v : BitVec 64) (s : StatusFlags) (pc : Int64),
    t.st = goto q.st { q.st.st.1 with regs := q.st.st.1.regs.setXReg .X4 v, status := s } pc
  rv : RegS 4 32 q.rview t.rview
  wv : RegS 4 32 q.wview t.wview
  grow : q.views.Grow t.views
  fwd : t.views.fwdb = q.views.fwdb
  xq : q.views.xclb = none
  xt : t.views.xclb = none
  prom : t.prom = q.prom

omit hv in
theorem SpRel.refl (q : Thread isa) (hx : q.views.xclb = none) : SpRel q q := by
  refine ⟨⟨q.st.st.1.regs.X4.toBitVec, q.st.st.1.status, q.st.st.2, ?_⟩, RegS.refl _ _ _, RegS.refl _ _ _,
    Views.Grow.refl _, rfl, hx, hx, rfl⟩
  rw [setXReg_X4_self]
  rfl

section Steps

variable {t : Thread isa} {mem : Memory} {outs : List (Except String (Outcome isa))} {oc : Outcome isa}
  (hS : SInv x o c t.st) (hs : stepOne Arch.armv8 t tid mem = some outs) (ho : .ok oc ∈ outs)

include hS hs ho

/-- `ldar w4,[x1]` (position 6): the read with its context, `X4 := v` with
the read's post-view. -/
theorem step_6 (hpc : t.st.st.2 = pcA 6) :
    ∃ ts v c' ν, (ts, v, c') ∈ readSuccs Arch.armv8 (instrViews t { addrRegs := [.x 1], loadDefs := [.x 4] })
        (ctx0 tid t mem) .acq false (L4 o) false ∧
      c'.loadViews = [ν] ∧ c'.mem = mem ∧ c'.prom = t.prom ∧ oc.mem = mem ∧ oc.thread =
      { t with
        st := goto t.st { t.st.st.1 with regs := t.st.st.1.regs.setXReg .X4 (BitVec.setWidth 64
          (BitVec.setWidth 32 v)) } (pcA 7)
        views := c'.views
        prom := c'.prom }.setRegView (.x 4) ν ν := by
  have hat := hS.st.at (by decide) (by decide) hpc
  obtain ⟨tree, st, c', hex, hr, hfi, hm⟩ := stepOne_fi Arch.armv8 hs ho
  rw [exec_ldar _ hat hS.st.x1 hS.st.dO] at hex
  obtain rfl := Option.some.inj hex
  rw [deps_6 _ hat] at hr hfi
  obtain ⟨ts, v, hx, rfl⟩ := run_load_ctx Arch.armv8 tid _ hr
  obtain ⟨t', v', hxe, -, -, -, -⟩ := (mem_readSuccs Arch.armv8).mp hx
  simp only [Prod.mk.injEq] at hxe
  obtain ⟨rfl, rfl, rfl⟩ := hxe
  have hlv := readNext_loadViews Arch.armv8 (instrViews t { addrRegs := [.x 1], loadDefs := [.x 4] })
    (ctx0 tid t mem) .acq false (L4 o) false ts v
  have hrw := readNext_rmwWrote Arch.armv8 (instrViews t { addrRegs := [.x 1], loadDefs := [.x 4] })
    (ctx0 tid t mem) .acq false (L4 o) false ts v
  exact ⟨ts, v, _, _, hx, hlv, readNext_mem _ _ _ _ _ _ _ _ _, readNext_prom _ _ _ _ _ _ _ _ _, hm,
    finishInstr_load1 rfl rfl rfl hrw rfl hlv hfi⟩

/-- `cmp w4,w3` (position 7) with a given result state: the flags' register
view is the join of `X4`'s and `X3`'s. -/
theorem step_7 (hpc : t.st.st.2 = pcA 7) {S : State} (hex : isa.exec t.st = some (.done S)) :
    oc.mem = mem ∧ oc.thread =
      { t with st := S, views := t.views, prom := t.prom }.setRegView .nzcv
        (max (max 0 (max (max 0 (t.rview[4]! : View)) t.rview[3]!)) 0)
        (max (max 0 (max (max 0 (t.wview[4]! : View)) t.wview[3]!)) 0) := by
  have hat := hS.st.at (by decide) (by decide) hpc
  obtain ⟨tree, st, c', hex', hr, hfi, hm⟩ := stepOne_fi Arch.armv8 hs ho
  rw [hex] at hex'
  obtain rfl := Option.some.inj hex'
  obtain ⟨rfl, rfl⟩ := run_done Arch.armv8 tid _ hr
  rw [deps_7 _ hat] at hfi
  exact ⟨hm, finishInstr_def1 rfl rfl rfl rfl rfl rfl hfi⟩

/-- `b.ne spin` (position 8): register views unchanged. -/
theorem step_8 (hpc : t.st.st.2 = pcA 8) : oc.thread.rview = t.rview ∧ oc.thread.wview = t.wview := by
  obtain ⟨tree, st, c', hex, hr, hfi, hm⟩ := stepOne_fi Arch.armv8 hs ho
  rw [deps_8 _ (hS.st.at (by decide) (by decide) hpc)] at hfi
  exact finishInstr_regs_nil rfl rfl rfl hfi

end Steps

/-! ## A spin step keeps the spin relation -/

section Core

variable {q t : Thread isa} {v0 : BitVec 64} {s0 : StatusFlags} {pc0 : Int64}
  (hc : t.st = goto q.st { q.st.st.1 with regs := q.st.st.1.regs.setXReg .X4 v0, status := s0 } pc0)
include hc

omit hv in
theorem core_X4 (v : BitVec 64) (pc : Int64) :
    goto t.st { t.st.st.1 with regs := t.st.st.1.regs.setXReg .X4 v } pc =
      goto q.st { q.st.st.1 with regs := q.st.st.1.regs.setXReg .X4 v, status := s0 } pc := by
  rw [hc]; simp [goto]

omit hv in
theorem core_status (s : StatusFlags) (pc : Int64) :
    goto t.st { t.st.st.1 with status := s } pc =
      goto q.st { q.st.st.1 with regs := q.st.st.1.regs.setXReg .X4 v0, status := s } pc := by
  rw [hc]

omit hv in
theorem core_goto (pc : Int64) :
    goto t.st t.st.st.1 pc = goto q.st { q.st.st.1 with regs := q.st.st.1.regs.setXReg .X4 v0, status := s0 } pc := by
  rw [hc]

end Core

/-- **A step of the spin loop** (positions 6–8) keeps memory and the spin
relation. -/
theorem spRel_step {q t : Thread isa} {mem : Memory} {outs : List (Except String (Outcome isa))}
    {oc : Outcome isa} (hR : SpRel q t) (hP : PI x o c t) (hs : stepOne Arch.armv8 t tid mem = some outs)
    (ho : .ok oc ∈ outs) (hpc : t.st.st.2 = pcA 6 ∨ t.st.st.2 = pcA 7 ∨ t.st.st.2 = pcA 8) :
    SpRel q oc.thread ∧ oc.mem = mem := by
  obtain ⟨hg, -, hnw⟩ := stepOne_grow Arch.armv8 hs ho
  obtain ⟨tree, -, -, hex, -⟩ := stepOne_fi Arch.armv8 hs ho
  have hxt := stepOne_xclb_none Arch.armv8 hex (noXcl hP.sinv tree hex) hs ho hP.xclb
  obtain ⟨v0, s0, pc0, hc⟩ := hR.core
  have gen : ∀ (hm : oc.mem = mem) (hp : oc.thread.prom = t.prom), (∃ (v : BitVec 64) (s : StatusFlags) (pc : Int64),
      oc.thread.st = goto q.st { q.st.st.1 with regs := q.st.st.1.regs.setXReg .X4 v, status := s } pc) →
      RegS 4 32 q.rview oc.thread.rview → RegS 4 32 q.wview oc.thread.wview → SpRel q oc.thread ∧ oc.mem = mem :=
    fun hm hp hcore hr hw => ⟨⟨hcore, hr, hw, hR.grow.trans hg, ((hnw (by rw [hm])).2 (by rw [hp])).1.trans hR.fwd,
      hR.xq, hxt, hp.trans hR.prom⟩, hm⟩
  rcases hpc with hpc | hpc | hpc
  · obtain ⟨ts, v, c', ν, -, -, -, hcp, hm, hoc⟩ := step_6 hP.sinv hs ho hpc
    refine gen hm (by rw [hoc]; exact hcp) ⟨_, s0, pcA 7, by rw [hoc]; exact core_X4 hc _ _⟩ ?_ ?_
    · rw [hoc]; simp only [Thread.setRegView, Array.set!_eq_setIfInBounds]; exact hR.rv.set (.inl rfl) _
    · rw [hoc]; simp only [Thread.setRegView, Array.set!_eq_setIfInBounds]; exact hR.wv.set (.inl rfl) _
  · obtain ⟨sf, hex7, -⟩ := exec_cmp _ (hP.sinv.st.at (by decide) (by decide) hpc)
    obtain ⟨hm, hoc⟩ := step_7 hP.sinv hs ho hpc hex7
    refine gen hm (by rw [hoc]; rfl) ⟨v0, sf, pcA 8, by rw [hoc]; exact core_status hc _ _⟩ ?_ ?_
    · rw [hoc]; simp only [Thread.setRegView, Array.set!_eq_setIfInBounds]; exact hR.rv.set (.inr rfl) _
    · rw [hoc]; simp only [Thread.setRegView, Array.set!_eq_setIfInBounds]; exact hR.wv.set (.inr rfl) _
  · obtain ⟨hm, hst, hp, -⟩ := s8 hP.sinv.st hs ho hpc
    obtain ⟨hrv, hwv⟩ := step_8 hP.sinv hs ho hpc
    exact gen hm hp ⟨v0, s0, _, by rw [hst]; exact core_goto hc _⟩ (hrv ▸ hR.rv) (hwv ▸ hR.wv)

/-! ## The cut at a second `LDAR` of a spin visit -/

/-- The dominated contexts of two spin states. -/
theorem ctx_dom {q t : Thread isa} (hR : SpRel q t) (mem : Memory) : (ctx0 tid q mem).Dom (ctx0 tid t mem) :=
  ⟨hR.grow.dom hR.fwd.symm (hR.xq.trans hR.xt.symm), hR.prom.symm, rfl, .nil, Nat.le_refl _, rfl, rfl⟩

/-- **The cut**: `q` (reached in `a₁` steps, at the `LDAR`) and the current
`t` (at the `LDAR` again, in the spin relation with `q`). The later `LDAR`
and the `CMP` after it replay from `q`, and the thread reached dominates the
thread after the later `CMP`; the run continues from there. -/
theorem cut_6 {t0 : Thread isa} {mem0 mem : Memory} {a₁ n : Nat} {q t : Thread isa} {r : Thread isa × Memory}
    (hq : ThreadNPn Arch.armv8 tid a₁ (t0, mem0) (q, mem)) (hqP : PI x o c q) (hqpc : q.st.st.2 = pcA 6)
    (hR : SpRel q t) (hP : PI x o c t) (hpc : t.st.st.2 = pcA 6)
    {outs : List (Except String (Outcome isa))} {oc : Outcome isa} (hs : stepOne Arch.armv8 t tid mem = some outs)
    (ho : .ok oc ∈ outs) {outs' : List (Except String (Outcome isa))} {oc' : Outcome isa}
    (hs' : stepOne Arch.armv8 oc.thread tid oc.mem = some outs') (ho' : .ok oc' ∈ outs')
    (hrun : ThreadNPn Arch.armv8 tid n (oc'.thread, oc'.mem) r) (hp : r.1.prom = []) :
    ∃ m, m ≤ a₁ + 2 + n ∧ CertOkN Arch.armv8 tid t0 mem0 m := by
  obtain ⟨ts, v, c', ν, hx, hlv, hcm, hcp, hm, hoc⟩ := step_6 hP.sinv hs ho hpc
  -- the read replays from `q`
  have hiv : (instrViews q { addrRegs := [.x 1], loadDefs := [.x 4] }).Dom
      (instrViews t { addrRegs := [.x 1], loadDefs := [.x 4] }) := by
    rw [instrViews_6, instrViews_6, hR.rv.2 1 (by decide) (by decide), hR.wv.2 1 (by decide) (by decide)]
    exact .refl _
  obtain ⟨c₂, hx₂, hd₂⟩ := readSuccs_dom Arch.armv8 hiv (ctx_dom hR mem) hx
  obtain ⟨t', v', hxe, -, -, -, -⟩ := (mem_readSuccs Arch.armv8).mp hx₂
  simp only [Prod.mk.injEq] at hxe
  obtain ⟨rfl, rfl, hc₂⟩ := hxe
  have hat := hqP.sinv.st.at (by decide) (by decide) hqpc
  have hex := exec_ldar _ hat hqP.sinv.st.x1 hqP.sinv.st.dO
  have hr : .ok (goto q.st { q.st.st.1 with regs := q.st.st.1.regs.setXReg .X4 (BitVec.setWidth 64
      (BitVec.setWidth 32 v)) } (pcA 7), c₂) ∈
      runTree Arch.armv8 tid (instrViews q (isa.deps q.st)) (ctx0 tid q mem) (.load .acq false (L4 o) fun v =>
        .done (goto q.st { q.st.st.1 with regs := q.st.st.1.regs.setXReg .X4 (BitVec.setWidth 64
          (BitVec.setWidth 32 v)) } (pcA 7))) := by
    rw [deps_6 _ hat]
    simp only [runTree, List.mem_flatMap]
    exact ⟨_, hx₂, run_done_exists Arch.armv8 tid (instrViews q { addrRegs := [.x 1], loadDefs := [.x 4] }) _ _⟩
  obtain ⟨ν₂, hlv₂⟩ : ∃ ν₂, c₂.loadViews = [ν₂] := ⟨_, by rw [hc₂, readNext_loadViews]; rfl⟩
  obtain ⟨q1, hq1⟩ : ∃ q1 : Thread isa, q1 = ({ q with
      st := goto q.st { q.st.st.1 with regs := q.st.st.1.regs.setXReg .X4 (BitVec.setWidth 64
        (BitVec.setWidth 32 v)) } (pcA 7)
      views := c₂.views
      prom := c₂.prom } : Thread isa).setRegView (.x 4) ν₂ ν₂ := ⟨_, rfl⟩
  have hrw₂ : c₂.rmwWrote = false := by rw [hc₂, readNext_rmwWrote]
  have hcm₂ : c₂.mem = mem := by rw [hc₂, readNext_mem]
  have hfi : q1 ∈ finishInstr q (isa.deps q.st) (instrViews q (isa.deps q.st))
      (goto q.st { q.st.st.1 with regs := q.st.st.1.regs.setXReg .X4 (BitVec.setWidth 64 (BitVec.setWidth 32 v)) }
        (pcA 7)) c₂ := by
    rw [deps_6 _ hat]
    unfold finishInstr
    simp only [hlv₂, hrw₂, List.foldl_nil, List.foldl_cons, List.length_singleton, Bool.and_false,
      Bool.false_eq_true, ↓reduceIte, List.mem_singleton]
    rw [hq1]
    try rfl
  obtain ⟨outs1, hs1, ho1⟩ := stepOne_of_fi Arch.armv8 hex hr hfi
  have hν : ν₂ ≤ ν := by
    have := hd₂.loadViews
    rw [hlv, hlv₂] at this
    cases this with
    | cons h1 h2 => exact h1
  -- the `CMP` from both
  have hpc7 : oc.thread.st.st.2 = pcA 7 := by rw [hoc]; rfl
  have hq1pc : q1.st.st.2 = pcA 7 := by rw [hq1]; rfl
  have hS1 := (step_sinv hP.sinv hs ho).1
  have hSq1 : SInv x o c q1.st := ⟨by rw [hq1]; exact hqP.sinv.st.goto _ _ rfl rfl rfl rfl, 7, by decide, hq1pc⟩
  have hat1 := hS1.st.at (by decide) (by decide) hpc7
  have hatq1 := hSq1.st.at (by decide) (by decide) hq1pc
  obtain ⟨v0, s0, pc0, hc⟩ := hR.core
  have hst1 : oc.thread.st = goto q.st { q.st.st.1 with
      regs := q.st.st.1.regs.setXReg .X4 (BitVec.setWidth 64 (BitVec.setWidth 32 v))
      status := s0 } (pcA 7) := by rw [hoc]; exact core_X4 hc _ _
  obtain ⟨sf, he1, he2⟩ := exec_cmp_pair oc.thread.st q1.st hat1 hatq1 (by rw [hst1, hq1]; rfl)
  rw [hm] at hs'
  obtain ⟨hm', hoc'⟩ := step_7 hS1 hs' ho' hpc7 he1
  obtain ⟨q2, hq2⟩ : ∃ q2 : Thread isa, q2 = ({ q1 with
      st := goto q1.st { q1.st.st.1 with status := sf } (pcA 8)
      views := q1.views
      prom := q1.prom } : Thread isa).setRegView .nzcv
        (max (max 0 (max (max 0 (q1.rview[4]! : View)) q1.rview[3]!)) 0)
        (max (max 0 (max (max 0 (q1.wview[4]! : View)) q1.wview[3]!)) 0) := ⟨_, rfl⟩
  have hfi2 : q2 ∈ finishInstr q1 (isa.deps q1.st) (instrViews q1 (isa.deps q1.st))
      (goto q1.st { q1.st.st.1 with status := sf } (pcA 8)) (ctx0 tid q1 mem) := by
    rw [deps_7 _ hatq1, hq2]
    exact List.mem_singleton.mpr rfl
  obtain ⟨outs2, hs2, ho2⟩ := stepOne_of_fi Arch.armv8 he2
    (run_done_exists Arch.armv8 tid (instrViews q1 (isa.deps q1.st)) (ctx0 tid q1 mem) _) hfi2
  -- the replayed thread dominates the thread after the later `CMP`
  have e1 : q1.rview = q.rview.setIfInBounds 4 ν₂ := by rw [hq1]; rfl
  have e2 : oc.thread.rview = t.rview.setIfInBounds 4 ν := by rw [hoc]; rfl
  have e1w : q1.wview = q.wview.setIfInBounds 4 ν₂ := by rw [hq1]; rfl
  have e2w : oc.thread.wview = t.wview.setIfInBounds 4 ν := by rw [hoc]; rfl
  have hd : q2.Dom oc'.thread := by
    rw [hoc', hq2]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show goto q1.st _ _ = goto oc.thread.st _ _
      rw [hst1, hq1]; simp [goto, Thread.setRegView]
    · simp only [Thread.setRegView, Array.set!_eq_setIfInBounds]
      rw [e1, e2]
      refine RegS.arrLe (RegS.refl _ _ _) hR.rv hν ?_
      have h4 := RegS.le (RegS.refl 4 32 q.rview) hR.rv hν 4 (by decide)
      have h3 := RegS.le (RegS.refl 4 32 q.rview) hR.rv hν 3 (by decide)
      simp only [View] at h4 h3 ⊢
      omega
    · simp only [Thread.setRegView, Array.set!_eq_setIfInBounds]
      rw [e1w, e2w]
      refine RegS.arrLe (RegS.refl _ _ _) hR.wv hν ?_
      have h4 := RegS.le (RegS.refl 4 32 q.wview) hR.wv hν 4 (by decide)
      have h3 := RegS.le (RegS.refl 4 32 q.wview) hR.wv hν 3 (by decide)
      simp only [View] at h4 h3 ⊢
      omega
    · show q1.views.Dom oc.thread.views
      rw [hq1, hoc]; exact hd₂.views
    · show q1.prom = oc.thread.prom
      rw [hq1, hoc]; exact hd₂.prom
  rw [hm'] at hrun
  obtain ⟨r', hr', hdr, -⟩ := hrun.dom (q2, mem) hd rfl
  refine ⟨a₁ + 2 + n, Nat.le_refl _, r'.1, r'.2, ?_, hdr.prom.trans hp⟩
  have h2 : ThreadNPn Arch.armv8 tid (a₁ + 1 + 1) (t0, mem0) (q2, mem) :=
    (hq.tail ⟨outs1, _, hs1, ho1, by rw [hcm₂]⟩).tail ⟨outs2, _, by rw [← hcm₂] at hs2 ⊢; exact hs2, ho2, rfl⟩
  exact h2.trans hr'

/-! ## The potential and the bound on a solo run -/

/-- The flag after a step from position `i` (`z`: the `Z` flag): set by an
`LDAR`, kept through `CMP` and a `B.NE` back to `spin`, dropped elsewhere. -/
def newFlag (i : Nat) (z h : Bool) : Bool :=
  if i = 6 then true else if i = 7 then h else if i = 8 then !z && h else false

/-- **The potential**: the longest solo run without a cut from position `i`
with `m` rounds left (`wn X7`), given whether an earlier `LDAR` of the current
spin visit is recorded (`h`). -/
def Φ : Nat → Nat → Bool → Nat
  | 1, m, _ => 12 * m + 2 | 3, m, _ => 12 * m + 1 | 4, m, _ => 12 * m
  | 6, m, false => 12 * m - 1 | 6, _, true => 1
  | 7, m, false => 12 * m + 1 | 7, m, true => 12 * m - 2
  | 8, m, false => 12 * m | 8, m, true => 12 * m - 3
  | 9, m, _ => 12 * m - 4 | 10, m, _ => 12 * m - 5 | 11, m, _ => 12 * m - 6 | 12, m, _ => 12 * m - 7
  | 13, m, _ => 12 * m - 8 | 14, m, _ => 12 * m - 9 | 15, m, _ => 12 * m + 2
  | _, _, _ => 0

omit layout hv in
/-- **Every step lowers the potential**, except a second `LDAR` of a spin
visit (`i = 6` with the flag set), which `cut_6` handles. -/
theorem Φ_step : ∀ i ∈ tkLoopPcs, ∀ (z : Bool) (m : Nat) (h : Bool), i ≠ 17 → ¬(i = 6 ∧ h = true) →
    (i ∈ [4, 6, 7, 8, 9, 10, 11, 12, 13, 14] → m ≠ 0) →
    Φ (nextPc z (decide (m = 0)) i) (if i = 14 then m - 1 else m) (newFlag i z h) + 1 ≤ Φ i m h := by
  intro i hi z m h h17 h6 hm
  simp only [tkLoopPcs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    by_cases hm0 : m = 0 <;> cases z <;> cases h <;>
    simp_all [Φ, nextPc, newFlag] <;> omega

omit layout hv in
theorem Φ_le (i m : Nat) : Φ i m false ≤ 12 * m + 2 := by
  unfold Φ; split <;> omega

/-- An earlier `LDAR` state `q` of the current spin visit, reached in fewer
than `a` steps, in the spin relation with the current thread. -/
def W6 (x o c : BitVec 64) (tid : Nat) (t0 : Thread isa) (mem0 : Memory) (a : Nat) (p : Thread isa × Memory) :
    Prop :=
  ∃ (q : Thread isa) (a₁ : Nat), a₁ < a ∧ ThreadNPn Arch.armv8 tid a₁ (t0, mem0) (q, p.2) ∧ PI x o c q ∧
    q.st.st.2 = pcA 6 ∧ SpRel q p.1

/-- **A solo run is bounded by `Φ`, or a shorter certification exists**:
induction along the run, carrying the prefix length `a` and the witness of
the current spin visit. -/
theorem run_bound {t0 : Thread isa} {mem0 : Memory} : ∀ (n : Nat) (p r : Thread isa × Memory),
    ThreadRun Arch.armv8 tid n p r → r.1.prom = [] → ∀ (a : Nat) (h : Bool),
    ThreadNPn Arch.armv8 tid a (t0, mem0) p → PI x o c p.1 → (h = true → W6 x o c tid t0 mem0 a p) →
    (∀ i ∈ tkLoopPcs, p.1.st.st.2 = pcA i → n ≤ Φ i (wn p.1.st.st.1.regs.X7) h) ∨
      ∃ m, m < a + n ∧ CertOkN Arch.armv8 tid t0 mem0 m := by
  intro n p r hr
  induction hr with
  | refl p => intro _ _ _ _ _ _; exact .inl fun _ _ _ => Nat.zero_le _
  | @step n p q r hs rest ih =>
    intro hp a h hpre hP hW
    obtain ⟨t, mem⟩ := p
    obtain ⟨outs, oc, hs, ho, rfl⟩ := hs
    simp only at hP hW hpre ⊢
    obtain ⟨i, hi, hpc⟩ := hP.sinv.pc
    have hpos : ∀ j ∈ tkLoopPcs, t.st.st.2 = pcA j → j = i := fun j hj e => addrOf_inj hj hi (e.symm.trans hpc)
    have hi17 : i ≠ 17 := fun e => by subst e; rw [stepOne_end hP.sinv.st hpc] at hs; cases hs
    obtain ⟨hP', hn, h7, h7'⟩ := pi_step hP hs ho hi hpc
    have hpre' : ThreadNPn Arch.armv8 tid (a + 1) (t0, mem0) (oc.thread, oc.mem) :=
      hpre.tail ⟨outs, oc, hs, ho, rfl⟩
    by_cases hcut : i = 6 ∧ h = true
    · -- a second `LDAR` of the visit: the run ends here, or the next `CMP` completes a cut
      obtain ⟨rfl, rfl⟩ := hcut
      cases rest with
      | refl => exact .inl fun j hj hj' => by obtain rfl := hpos j hj hj'; simp [Φ]
      | step hs2 rest2 =>
        obtain ⟨outs', oc', hs', ho', rfl⟩ := hs2
        obtain ⟨q, a₁, ha, hq, hqP, hqpc, hR⟩ := hW rfl
        obtain ⟨m, hm, hc⟩ := cut_6 hq hqP hqpc hR hP hpc hs ho hs' ho' rest2.toNPn hp
        exact .inr ⟨m, by omega, hc⟩
    · have hW' : newFlag i t.st.st.1.status.z h = true →
          W6 x o c tid t0 mem0 (a + 1) (oc.thread, oc.mem) := by
        intro hf
        unfold newFlag at hf
        by_cases e6 : i = 6
        · subst e6
          obtain ⟨hR', hm⟩ := spRel_step (SpRel.refl t hP.xclb) hP hs ho (.inl hpc)
          exact ⟨t, a, Nat.lt_succ_self _, by rw [hm]; exact hpre, hP, hpc, hR'⟩
        · by_cases e7 : i = 7
          · subst e7
            simp only [e6, ↓reduceIte] at hf
            obtain ⟨q, a₁, ha, hq, hqP, hqpc, hR⟩ := hW hf
            obtain ⟨hR', hm⟩ := spRel_step hR hP hs ho (.inr (.inl hpc))
            exact ⟨q, a₁, by omega, by rw [hm]; exact hq, hqP, hqpc, hR'⟩
          · by_cases e8 : i = 8
            · subst e8
              simp only [e6, e7, ↓reduceIte, Bool.and_eq_true] at hf
              obtain ⟨q, a₁, ha, hq, hqP, hqpc, hR⟩ := hW hf.2
              obtain ⟨hR', hm⟩ := spRel_step hR hP hs ho (.inr (.inr hpc))
              exact ⟨q, a₁, by omega, by rw [hm]; exact hq, hqP, hqpc, hR'⟩
            · simp [e6, e7, e8] at hf
      rcases ih hp (a + 1) _ hpre' hP' hW' with hb | ⟨m, hm, hc⟩
      · refine .inl fun j hj hj' => ?_
        obtain rfl := hpos j hj hj'
        have hb' := hb _ (nextPc_mem _ _ j hj) hn
        have hst := Φ_step j hj t.st.st.1.status.z (wn t.st.st.1.regs.X7) h hi17 hcut (fun hm => hP.x7 j hm hpc)
        have e : wn oc.thread.st.st.1.regs.X7 = if j = 14 then wn t.st.st.1.regs.X7 - 1 else wn t.st.st.1.regs.X7 := by
          split
          · have := h7' ‹_›; omega
          · exact h7 ‹_›
        rw [e] at hb'
        omega
      · exact .inr ⟨m, by omega, hc⟩

/-- **Every certification of a worker is within `12 * k + 2` instructions**,
when it has at most `k` rounds left. -/
theorem certOkN_bound {t : Thread isa} {mem : Memory} {k : Nat} (hP : PI x o c t)
    (hk : wn t.st.st.1.regs.X7 ≤ k) {n : Nat} (h : CertOkN Arch.armv8 tid t mem n) :
    CertOkN Arch.armv8 tid t mem (12 * k + 2) := by
  refine CertOkN.bound_of_shorter _ (fun n r hr hp hn => ?_) h
  obtain ⟨i, hi, hpc⟩ := hP.sinv.pc
  rcases run_bound n (t, mem) r hr hp 0 false (.refl _ _) hP (fun h => Bool.noConfusion h) with hb | ⟨m, hm, hc⟩
  · have h1 : n ≤ Φ i (wn t.st.st.1.regs.X7) false := hb i hi hpc
    have h2 := Φ_le i (wn t.st.st.1.regs.X7)
    omega
  · exact ⟨m, by omega, hc⟩

/-! ## Reachable configurations -/

/-- No thread has a pending load exclusive (none of the worker's cells
performs one). -/
def XclbNone (cfg : Config isa) : Prop := ∀ (i : Nat) u, cfg.threads[i]? = some u → u.views.xclb = none

theorem xclbNone_step {fuel k N : Nat} {cfg cfg' : Config isa} (hI : TicketLoopInvP.LInv k N x o c cfg)
    (h : XclbNone cfg) {tid : Nat} (hst : StepSem Arch.armv8 fuel tid cfg cfg') : XclbNone cfg' := by
  rcases hst with ⟨t, outs, oc, ht, hs, ho, -, rfl⟩ | ⟨t, w, ht, -, -, rfl⟩
  · intro i u hu
    rcases wt_get ht hu with ⟨rfl, rfl⟩ | ⟨-, hu⟩
    · have hS := (hI.thr _ t ht).ti.sinv
      obtain ⟨tree, -, -, hex, -⟩ := stepOne_fi Arch.armv8 hs ho
      exact stepOne_xclb_none Arch.armv8 hex (noXcl hS tree hex) hs ho (h _ t ht)
    · exact h i u hu
  · intro i u hu
    rcases wt_get ht hu with ⟨rfl, rfl⟩ | ⟨-, hu⟩
    · exact h _ t ht
    · exact h i u hu

omit layout hv in
theorem xclbNone_init (states : List isa.State) (initMem : List (Loc × Val)) :
    XclbNone (Config.init states initMem) := by
  intro i u hu
  simp only [Config.init, List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at hu
  obtain ⟨s, -, rfl⟩ := hu
  rfl

/-- **Bounded certification from every start configuration**:
`F = 12 * k + 2`, for `k` rounds per worker. -/
theorem ticket_loop_certBounded {k N : Nat} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : TkLoopStart k N x o c states initMem) :
    CertBoundedFrom Arch.armv8 (Config.init states initMem) (12 * k + 2) := by
  intro fuel cfg hr tid t n ht hc
  have hinv := NoStuck.reachableSem_inv (fun cfg => TicketLoopInvP.LInv k N x o c cfg ∧ XclbNone cfg)
    (fun tid cfg cfg' ⟨hI, hX⟩ hst => by
      obtain ⟨t, ht⟩ : ∃ t, cfg.threads[tid]? = some t := by
        rcases hst with ⟨t, -, -, ht, -⟩ | ⟨t, -, ht, -⟩ <;> exact ⟨t, ht⟩
      exact ⟨(TicketLoopInvP.inv_step hI ht hst).1, xclbNone_step hI hX hst⟩) hr
    ⟨TicketLoopInvP.inv_init hs, xclbNone_init _ _⟩
  have hT := (hinv.1.thr tid t ht).ti
  exact certOkN_bound ⟨hT.sinv, hT.x7, hinv.2 tid t ht⟩ hT.k7 hc

/-! ## The fuel-free theorems -/

/-- `TicketLoop.TicketLoopStarveSem` on the fuel-free semantic machine:
starvation-freedom per round. -/
def TicketLoopStarveSemU : Prop :=
  ∀ k N x o c states initMem, TkLoopStart k N x o c states initMem → ∀ r,
    LiveFromSemU Arch.armv8 (Config.init states initMem)
      (fun cfg => WeakFairSemU Arch.armv8 cfg ∧ MemFair Arch.armv8 cfg) (TkLoopWaiting k r) (TkLoopDone k r)

/-- `TicketLoop.TicketLoopFinishSem` on the fuel-free semantic machine: every
thread completes all its rounds. -/
def TicketLoopFinishSemU : Prop :=
  ∀ k N x o c states initMem, TkLoopStart k N x o c states initMem →
    LiveFromSemU Arch.armv8 (Config.init states initMem)
      (fun cfg => WeakFairSemU Arch.armv8 cfg ∧ MemFair Arch.armv8 cfg) TkLoopPresent TkLoopFinished

/-- `TicketLoop.TicketLoopLiveSem` on the fuel-free semantic machine. -/
def TicketLoopLiveSemU : Prop := TicketLoopStarveSemU ∧ TicketLoopFinishSemU

/-- `TicketLoop.TicketLoopTermSem` on the fuel-free semantic machine: every
fair trace reaches a final configuration. -/
def TicketLoopTermSemU : Prop :=
  ∀ k N x o c states initMem, TkLoopStart k N x o c states initMem →
    TermFromSemU Arch.armv8 (Config.init states initMem)
      (fun cfg => WeakFairSemU Arch.armv8 cfg ∧ MemFair Arch.armv8 cfg)

/-- **Starvation-freedom per round, fuel-free**: `ticket_loop_starve_sem` at
fuel `12 * k + 2` through `liveTransfer`. -/
theorem ticket_loop_starve_semU : TicketLoopStarveSemU := fun k N x o c states initMem hs r =>
  liveTransfer (ticket_loop_certBounded hs)
    (TicketLoopSem.ticket_loop_starve_sem (12 * k + 2) k N x o c states initMem hs r)

/-- **Every thread completes all its rounds, fuel-free.** -/
theorem ticket_loop_finish_semU : TicketLoopFinishSemU := fun k N x o c states initMem hs =>
  liveTransfer (ticket_loop_certBounded hs)
    (TicketLoopSem.ticket_loop_finish_sem (12 * k + 2) k N x o c states initMem hs)

/-- **Repeated-acquire ticket-lock liveness, fuel-free** (promises
included): starvation-freedom per round and completion of all rounds, under
fuel-free weak fairness and memory fairness. -/
theorem ticket_loop_live_semU : TicketLoopLiveSemU := ⟨ticket_loop_starve_semU, ticket_loop_finish_semU⟩

/-- **Termination, fuel-free**: `ticket_loop_term_sem` at fuel `12 * k + 2`
through `termFromTransfer` (the existing statement is termination under
fairness, `Term.TermFromSem`, not a bound for every schedule). -/
theorem ticket_loop_term_semU : TicketLoopTermSemU := fun k N x o c states initMem hs =>
  termFromTransfer (ticket_loop_certBounded hs)
    (TicketLoopSem.ticket_loop_term_sem (12 * k + 2) k N x o c states initMem hs)

omit layout hv in
/-- `ticket_loop_live_semU` at the concrete layout `TicketLoopPF.tkLoopLayout`. -/
theorem ticket_loop_live_semU_concrete : @TicketLoopLiveSemU tkLoopLayout :=
  @ticket_loop_live_semU tkLoopLayout tkLoopValid

omit layout hv in
/-- `ticket_loop_term_semU` at the concrete layout. -/
theorem ticket_loop_term_semU_concrete : @TicketLoopTermSemU tkLoopLayout :=
  @ticket_loop_term_semU tkLoopLayout tkLoopValid

end Kraken.Promising.Live.CertBoundedTicketLoop

#print axioms Kraken.Promising.Live.CertBoundedTicketLoop.ticket_loop_live_semU_concrete
#print axioms Kraken.Promising.Live.CertBoundedTicketLoop.ticket_loop_term_semU_concrete
