/-
**Bounded certification for the AArch64 CAS spinlock**
(`casTtasWorker`, valid layout): `CertBoundedFrom Arch.armv8 c0 13` for every
`Spin.CasStart` configuration, and the fuel-free liveness theorems
`spin_cas_live{,_oneShot}_semU{,_concrete}`.

**Route R3 through the iteration cut** (`LiveCertCut`):
a certifying solo run of a worker longer than `F = 13` instructions is not
the shortest one. Before its first write (a successful `CASA`, or a store of
the critical section) the run stays in the try/spin loop, where only `X2`
changes (value and register view); its scalar views only grow
(`stepOne_grow`). Two kinds of repetition shorten it:

- **two visits of the `CASA` cell** (position 4) that both come from the
  `MOV W2,#0`: the same machine state (`X2 = 0`), the same promises and
  memory, `X2`'s register view `0` at both, the other registers' views
  unchanged, scalar views grown — so the earlier visit *dominates*
  (`Thread.Dom`) the later and the loop between them is cut
  (`ThreadNPn.dom`);
- **two `LDR W2,[X0]` steps**: the later read (its timestamp and value)
  replays from the earlier `LDR` state with lower views (`readSuccs_dom`),
  and the thread after that replay dominates the thread after the later
  read; the spin between the two loads is cut.

A run without either repetition is at most `13` instructions long (the
potential `Φ`, computed from the loop automaton: at most one `LDR` step and
one `MOV`-reached `CASA` cell before the write, then at most 7 steps to the
end). `F` depends on the program only: not on the fuel, the thread count or
the layout.

Register views: an instruction resets its destinations' views, so they are
not monotone along a run; the loop cells' dependencies (`deps_3` … `deps_9`,
read from the code like the event trees of `LiveSpinCasTrees`) show that
every loop cell writes `X2` at most (`RegX2`), and `MOV W2,#0` gives it view
`0`.

Names: `casDepsOk`, `Core`, `RegX2`, `LInv`, `Φ`, `tail_bound`, `loop_bound`,
`certOkN_bound`, `cas_certBounded`, `CasSpinLiveSemU`,
`CasSpinLiveOneShotSemU`, `spin_cas_live_semU`, `spin_cas_live_oneShot_semU`
and their `_concrete` forms.
-/
import Kraken.Promising.LiveCertBounded
import Kraken.Promising.LiveCertCut
import Kraken.Promising.LiveSpinSemCas

namespace Kraken.Promising.Live.CertBoundedSpinCas

set_option linter.unusedSectionVars false

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live
open Kraken.Promising.Live.SpinCasTrees Kraken.Promising.Live.TicketStep Kraken.Promising.Live.SpinStep
open Kraken.Promising.Live.SemShape Kraken.Promising.Live.Sem Kraken.Promising.Live.SpinSemSolo
open Kraken.Promising.Live.SpinSemInv Kraken.Promising.Live.CertBounded Kraken.Promising.Live.CertCut
open Kraken.Promising.Live.SpinCasInv (Static Holder stepOne_end s5 s8 s9 s11 s12 s15)
open Kraken.Promising.Live.TicketInv (L4)
open Kraken.Promising.SLR.EnvG.CasSmoke (casTtasWorker)

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout casTtasWorker)]

set_option hygiene false in
local notation "pcA" => (layout casTtasWorker).addrOf

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

/-! ## The dependencies of the loop cells -/

omit hv in
/-- A thread state's directive is its code's first cell (as
`EnvG.directive_of_codeAt`, `A64MaskCore.lean`, not imported here). -/
theorem directive_of_codeAt {st : State} {d : Directive} {z : Nat} {rest : List (Directive × Nat)}
    (hcode : Kraken.Executable.codeAt st.exe st.st.2 = (d, z) :: rest) : st.directive = some d := by
  obtain ⟨exe, endPc, ⟨s, pc⟩, showPc, decls⟩ := st
  unfold State.directive
  simp only at hcode ⊢
  rw [show List.dropWhile _ (Kraken.Executable.directivesFromAddress exe pc) = Kraken.Executable.codeAt exe pc from by
    unfold Kraken.Executable.codeAt
    congr 1, hcode]
  rfl

/-- Read the dependencies of the cell at position `i` (the `a64cell` recipe). -/
local macro "a64deps" h:ident i:num : tactic => `(tactic| (
  have hc := Kraken.Executable.codeAt_addrOf (p := casTtasWorker) (i := $i) (d := casTtasWorker[$i])
    (by decide) (by decide)
  rw [← ($h).pc] at hc
  generalize hd : casTtasWorker[$i] = d at hc
  simp only [casTtasWorker, List.getElem_cons_succ, List.getElem_cons_zero] at hd
  subst hd
  have hdir := directive_of_codeAt (by rw [($h).exe]; exact hc)
  show AArch64.deps _ = _
  unfold AArch64.deps
  rw [hdir]
  rfl))

/-- The loop cells' dependencies: `mov w2,#0`, `casa w2,w3,[x0]`, `cbz w2`,
`ldr w2,[x0]`, `cbnz w2`, `b try`. -/
theorem deps_3 (st : State) (h : At st 3) : isa.deps st = { defs := [.x 2] } := by a64deps h 3
theorem deps_4 (st : State) (h : At st 4) : isa.deps st =
    { dataRegs := [.x 3], condRegs := [.x 2], addrRegs := [.x 0], loadDefs := [.x 2], casLike := true } := by
  a64deps h 4
theorem deps_5 (st : State) (h : At st 5) : isa.deps st = { condRegs := [.x 2], isBranch := true } := by a64deps h 5
theorem deps_7 (st : State) (h : At st 7) : isa.deps st = { addrRegs := [.x 0], loadDefs := [.x 2] } := by a64deps h 7
theorem deps_8 (st : State) (h : At st 8) : isa.deps st = { condRegs := [.x 2], isBranch := true } := by a64deps h 8
theorem deps_9 (st : State) (h : At st 9) : isa.deps st = {} := by a64deps h 9

/-! ## Only `X2` changes in the loop -/

omit hv in
theorem setXReg_X2_X2 (r : Reg64s) (a b : BitVec 64) : (r.setXReg .X2 a).setXReg .X2 b = r.setXReg .X2 b := by
  simp [Reg64s.setXReg]

omit hv in
theorem setXReg_X2_self (r : Reg64s) : r.setXReg .X2 r.X2.toBitVec = r := by
  simp [Reg64s.setXReg]

/-- The machine state of a loop state: `s0`'s with `X2` replaced, at some pc. -/
def Core (s0 s : State) : Prop :=
  ∃ x pc, s = goto s0 { s0.st.1 with regs := s0.st.1.regs.setXReg .X2 x } pc

omit hv in
theorem Core.self (s0 : State) : Core s0 s0 :=
  ⟨s0.st.1.regs.X2.toBitVec, s0.st.2, by rw [setXReg_X2_self]⟩

omit hv in
/-- `goto` with `X2` set, from a `Core` state: its normal form. -/
theorem Core.set {s0 s : State} (h : Core s0 s) (v : BitVec 64) (pc' : Int64) :
    goto s { s.st.1 with regs := s.st.1.regs.setXReg .X2 v } pc' =
      goto s0 { s0.st.1 with regs := s0.st.1.regs.setXReg .X2 v } pc' := by
  obtain ⟨x, pc, rfl⟩ := h
  simp [goto]

omit hv in
theorem Core.set' {s0 s : State} (h : Core s0 s) (v : BitVec 64) (pc' : Int64) :
    Core s0 (goto s { s.st.1 with regs := s.st.1.regs.setXReg .X2 v } pc') :=
  ⟨v, pc', h.set v pc'⟩

omit hv in
theorem Core.goto {s0 s : State} (h : Core s0 s) (pc' : Int64) : Core s0 (goto s s.st.1 pc') := by
  obtain ⟨x, pc, rfl⟩ := h
  exact ⟨x, pc', rfl⟩

/-- Register-view arrays that differ from `base` at most in `X2`'s slot. -/
def RegX2 (base a : Array View) : Prop := a = base ∨ ∃ ν, a = base.setIfInBounds 2 ν

omit hv in
theorem RegX2.set {base a : Array View} (h : RegX2 base a) (ν : View) :
    a.setIfInBounds 2 ν = base.setIfInBounds 2 ν := by
  rcases h with rfl | ⟨ν', rfl⟩
  · rfl
  · exact Array.setIfInBounds_setIfInBounds _

omit hv in
theorem RegX2.set' {base a : Array View} (h : RegX2 base a) (ν : View) : RegX2 base (a.setIfInBounds 2 ν) :=
  .inr ⟨ν, h.set ν⟩

omit hv in
/-- `X0`'s view is `base`'s. -/
theorem RegX2.get0 {base a : Array View} (h : RegX2 base a) : (a[0]! : View) = base[0]! := by
  rcases h with rfl | ⟨ν, rfl⟩
  · rfl
  · simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]

omit hv in
theorem instrViews_7 (t : Thread isa) :
    instrViews t { addrRegs := [.x 0], loadDefs := [.x 2] } =
      { addrR := max 0 (t.rview[0]! : View), addrW := max 0 (t.wview[0]! : View), dataR := 0, dataW := 0,
        condW := 0 } := rfl

/-! ## The loop invariant and the witnesses -/

variable {l c : BitVec 64} {tid : Nat}

/-- **The loop invariant**, relative to the thread `s0` at the start of the
write-free stretch: a loop cell, `SInv`, `Core`, only `X2`'s register views
changed, scalar views grown, the forwarding table, promises and memory
unchanged, no pending load exclusive. -/
structure LInv (l c : BitVec 64) (s0 : Thread isa) (mem : Memory) (t : Thread isa) : Prop where
  pos : ∃ i ∈ [3, 4, 5, 7, 8, 9], t.st.st.2 = pcA i
  sinv : SInv l c t.st
  core : Core s0.st t.st
  rv : RegX2 s0.rview t.rview
  wv : RegX2 s0.wview t.wview
  grow : s0.views.Grow t.views
  fwd : t.views.fwdb = s0.views.fwdb
  xclb : t.views.xclb = none
  prom : t.prom = s0.prom

/-- An earlier `LDR` state `q` (reached in `a₁` steps), with views grown up to
the current thread. -/
def W7 (l c : BitVec 64) (tid : Nat) (s0 : Thread isa) (mem : Memory) (a : Nat) (cur : Thread isa) : Prop :=
  ∃ (q : Thread isa) (a₁ : Nat), a₁ < a ∧ ThreadNPn Arch.armv8 tid a₁ (s0, mem) (q, mem) ∧ LInv l c s0 mem q ∧
    q.st.st.2 = pcA 7 ∧ q.views.Grow cur.views

/-- An earlier `MOV`-reached `CASA` state `q`, with views grown up to the
current thread. -/
def W4 (l c : BitVec 64) (tid : Nat) (s0 : Thread isa) (mem : Memory) (a : Nat) (cur : Thread isa) : Prop :=
  ∃ (q : Thread isa) (a₁ : Nat), a₁ ≤ a ∧ ThreadNPn Arch.armv8 tid a₁ (s0, mem) (q, mem) ∧ LInv l c s0 mem q ∧
    q.st = goto s0.st { s0.st.st.1 with regs := s0.st.st.1.regs.setXReg .X2 0#64 } (pcA 4) ∧
    q.rview = s0.rview.setIfInBounds 2 0 ∧ q.wview = s0.wview.setIfInBounds 2 0 ∧ q.views.Grow cur.views

/-- **The potential**: the longest run without a repetition from a loop cell,
given whether an `LDR` step (`h7`) and a `MOV`-reached `CASA` cell (`h4`)
have been seen. -/
def Φ : Nat → Bool → Bool → Nat
  | 3, _, true => 0 | 3, _, false => 8
  | 4, _, true => 7 | 4, true, false => 7 | 4, false, false => 13
  | 5, true, _ => 6 | 5, false, true => 6 | 5, false, false => 12
  | 7, true, _ => 0 | 7, false, true => 3 | 7, false, false => 11
  | 8, true, true => 2 | 8, false, true => 4 | 8, true, false => 10 | 8, false, false => 12
  | 9, _, true => 1 | 9, _, false => 9
  | _, _, _ => 0

omit hv in
theorem Φ_le (i : Nat) (h7 h4 : Bool) : Φ i h7 h4 ≤ 13 := by
  unfold Φ; split <;> omega

/-! ## The straight line after the loop -/

/-- The remaining steps from `cbz` with `X2 = 0` and from the critical
section on. -/
def Ψ : Nat → Nat
  | 5 => 6 | 11 => 5 | 12 => 4 | 13 => 3 | 14 => 2 | 15 => 1 | _ => 0

/-- **The tail**: from `cbz` with `X2 = 0`, or from the critical section on,
a solo run has at most `Ψ i ≤ 6` instructions. -/
theorem tail_bound : ∀ (n : Nat) (p r : Thread isa × Memory), ThreadRun Arch.armv8 tid n p r → SInv l c p.1.st →
    ∀ i ∈ [5, 11, 12, 13, 14, 15, 17], p.1.st.st.2 = pcA i → (i = 5 → w32 p.1.st.st.1.regs.X2 = 0#32) →
    n ≤ Ψ i := by
  intro n p r h
  induction h with
  | refl p => intro _ i _ _ _; exact Nat.zero_le _
  | @step n p q r hs _ ih =>
    intro hS i hi hpc hz
    obtain ⟨outs, oc, hs, ho, rfl⟩ := hs
    have hS' := (step_sinv hS hs ho).1
    have no5 : ∀ j, j ≠ 5 → (j = 5 → w32 oc.thread.st.st.1.regs.X2 = 0#32) := fun j hj h => absurd h hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨-, hst, -⟩ := s5 hS.st hs ho hpc
      rw [ite_eq_left (hz rfl)] at hst
      have := ih hS' 11 (by decide) (by rw [hst]) (no5 11 (by decide))
      simp only [Ψ] at this ⊢; omega
    · have h11 := s11 hS.st hs ho hpc
      obtain ⟨ts, v, hst, -⟩ := h11
      have := ih hS' 12 (by decide) (by rw [hst]) (no5 12 (by decide))
      simp only [Ψ] at this ⊢; omega
    · obtain ⟨-, hst, -⟩ := s12 hS.st hs ho hpc
      have := ih hS' 13 (by decide) (by rw [hst]) (no5 13 (by decide))
      simp only [Ψ] at this ⊢; omega
    · obtain ⟨hst, -⟩ := s13p hS.st hs ho hpc
      have := ih hS' 14 (by decide) (by rw [hst]) (no5 14 (by decide))
      simp only [Ψ] at this ⊢; omega
    · obtain ⟨hst, -⟩ := s14p hS.st hs ho hpc
      have := ih hS' 15 (by decide) (by rw [hst]) (no5 15 (by decide))
      simp only [Ψ] at this ⊢; omega
    · obtain ⟨-, hst, -⟩ := s15 hS.st hs ho hpc
      have := ih hS' 17 (by decide) (by rw [hst]) (no5 17 (by decide))
      simp only [Ψ] at this ⊢; omega
    · rw [stepOne_end hS.st hpc] at hs; cases hs

/-! ## One loop step -/

section Steps

variable {t : Thread isa} {mem : Memory} {outs : List (Except String (Outcome isa))} {oc : Outcome isa}
  (hS : SInv l c t.st) (hs : stepOne Arch.armv8 t tid mem = some outs) (ho : .ok oc ∈ outs)

include hS hs ho

/-- The generic facts of a loop step: `SInv`, views grown, no pending
exclusive, and, without a write, forwarding and promises unchanged. -/
theorem step_gen (hnx : ∀ tree, isa.exec t.st = some tree → tree.NoXclLoad) (hx : t.views.xclb = none) :
    SInv l c oc.thread.st ∧ t.views.Grow oc.thread.views ∧ oc.thread.views.xclb = none ∧
      (oc.mem = mem → oc.thread.prom = t.prom → oc.thread.views.fwdb = t.views.fwdb) := by
  obtain ⟨tree, -, -, hex, -⟩ := stepOne_fi Arch.armv8 hs ho
  obtain ⟨hg, -, hnw⟩ := stepOne_grow Arch.armv8 hs ho
  refine ⟨(step_sinv hS hs ho).1, hg, stepOne_xclb_none Arch.armv8 hex (hnx tree hex) hs ho hx, fun hm hp => ?_⟩
  exact ((hnw (by rw [hm])).2 (by rw [hp])).1

/-- `mov w2,#0` (position 3): `X2 := 0`, with register view `0`. -/
theorem step_3 (hpc : t.st.st.2 = pcA 3) : oc.mem = mem ∧ oc.thread =
    { t with
      st := goto t.st { t.st.st.1 with regs := t.st.st.1.regs.setXReg .X2 0#64 } (pcA 4)
      views := t.views
      prom := t.prom }.setRegView (.x 2) 0 0 := by
  have hat := hS.st.at (by decide) (by decide) hpc
  obtain ⟨tree, st, c', hex, hr, hfi, hm⟩ := stepOne_fi Arch.armv8 hs ho
  rw [exec_mov2 _ hat] at hex
  obtain rfl := Option.some.inj hex
  obtain ⟨rfl, rfl⟩ := run_done Arch.armv8 tid _ hr
  rw [deps_3 _ hat] at hfi
  exact ⟨hm, finishInstr_def1 rfl rfl rfl rfl rfl rfl hfi⟩

/-- `casa` (position 4): failing, the read with its context (`X2 := old ≠ 0`);
succeeding, position 5 with `X2 = 0`. -/
theorem step_4 (hpc : t.st.st.2 = pcA 4) (hz : w32 t.st.st.1.regs.X2 = 0#32) :
    (∃ tr old c' ν, (tr, old, c') ∈ readSuccs Arch.armv8 (instrViews t
        { dataRegs := [.x 3], condRegs := [.x 2], addrRegs := [.x 0], loadDefs := [.x 2], casLike := true })
        (ctx0 tid t mem) (Arch.armv8.rmwKind .acq).loadKind false (L4 l) false ∧
      c'.loadViews = [ν] ∧ c'.mem = mem ∧ c'.prom = t.prom ∧ oc.mem = mem ∧ oc.thread =
      { t with
        st := goto t.st { t.st.st.1 with regs := t.st.st.1.regs.setXReg .X2 (BitVec.setWidth 64
          (BitVec.setWidth 32 old)) } (pcA 5)
        views := c'.views
        prom := c'.prom }.setRegView (.x 2) ν ν) ∨
    (oc.thread.st.st.2 = pcA 5 ∧ w32 oc.thread.st.st.1.regs.X2 = 0#32) := by
  have hat := hS.st.at (by decide) (by decide) hpc
  obtain ⟨tree, st, c', hex, hr, hfi, hm⟩ := stepOne_fi Arch.armv8 hs ho
  rw [exec_casa _ hat hS.st.x0 hS.st.dl] at hex
  obtain rfl := Option.some.inj hex
  rw [deps_4 _ hat] at hr hfi
  obtain ⟨tr, old, c1, hx, rfl, hc⟩ := run_rmwo_ctx Arch.armv8 tid _ rfl hr
  have hst : oc.thread.st =
      goto t.st { t.st.st.1 with regs := t.st.st.1.regs.setXReg .X2 (BitVec.setWidth 64 (BitVec.setWidth 32 old)) }
        (pcA 5) := finishInstr_st hfi
  by_cases e : BitVec.setWidth 32 old = w32 t.st.st.1.regs.X2
  · right
    refine ⟨by rw [hst], ?_⟩
    rw [hst]
    show BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 old)) = 0#32
    rw [e, hz]; decide
  · left
    have hc' : c' = c1 := hc (by simp [e])
    subst hc'
    obtain ⟨t', v', hxe, -, -, -, -⟩ := (mem_readSuccs Arch.armv8).mp hx
    simp only [Prod.mk.injEq] at hxe
    obtain ⟨rfl, rfl, hc1⟩ := hxe
    subst hc1
    have hlv := readNext_loadViews Arch.armv8 (instrViews t
      { dataRegs := [.x 3], condRegs := [.x 2], addrRegs := [.x 0], loadDefs := [.x 2], casLike := true })
      (ctx0 tid t mem) (Arch.armv8.rmwKind .acq).loadKind false (L4 l) false tr old
    have hrw := readNext_rmwWrote Arch.armv8 (instrViews t
      { dataRegs := [.x 3], condRegs := [.x 2], addrRegs := [.x 0], loadDefs := [.x 2], casLike := true })
      (ctx0 tid t mem) (Arch.armv8.rmwKind .acq).loadKind false (L4 l) false tr old
    refine ⟨tr, old, _, _, hx, hlv, readNext_mem _ _ _ _ _ _ _ _ _, readNext_prom _ _ _ _ _ _ _ _ _, hm, ?_⟩
    exact finishInstr_load1 rfl rfl rfl hrw rfl hlv hfi

/-- `ldr w2,[x0]` (position 7): the read with its context, `X2 := v` with
the read's post-view. -/
theorem step_7 (hpc : t.st.st.2 = pcA 7) :
    ∃ ts v c' ν, (ts, v, c') ∈ readSuccs Arch.armv8 (instrViews t { addrRegs := [.x 0], loadDefs := [.x 2] })
        (ctx0 tid t mem) .plain false (L4 l) false ∧
      c'.loadViews = [ν] ∧ c'.mem = mem ∧ c'.prom = t.prom ∧ oc.mem = mem ∧ oc.thread =
      { t with
        st := goto t.st { t.st.st.1 with regs := t.st.st.1.regs.setXReg .X2 (BitVec.setWidth 64
          (BitVec.setWidth 32 v)) } (pcA 8)
        views := c'.views
        prom := c'.prom }.setRegView (.x 2) ν ν := by
  have hat := hS.st.at (by decide) (by decide) hpc
  obtain ⟨tree, st, c', hex, hr, hfi, hm⟩ := stepOne_fi Arch.armv8 hs ho
  rw [exec_ldr_l _ hat hS.st.x0 hS.st.dl] at hex
  obtain rfl := Option.some.inj hex
  rw [deps_7 _ hat] at hr hfi
  obtain ⟨ts, v, hx, rfl⟩ := run_load_ctx Arch.armv8 tid _ hr
  obtain ⟨t', v', hxe, -, -, -, -⟩ := (mem_readSuccs Arch.armv8).mp hx
  simp only [Prod.mk.injEq] at hxe
  obtain ⟨rfl, rfl, rfl⟩ := hxe
  have hlv := readNext_loadViews Arch.armv8 (instrViews t { addrRegs := [.x 0], loadDefs := [.x 2] }) (ctx0 tid t mem)
    .plain false (L4 l) false ts v
  have hrw := readNext_rmwWrote Arch.armv8 (instrViews t { addrRegs := [.x 0], loadDefs := [.x 2] }) (ctx0 tid t mem)
    .plain false (L4 l) false ts v
  exact ⟨ts, v, _, _, hx, hlv, readNext_mem _ _ _ _ _ _ _ _ _, readNext_prom _ _ _ _ _ _ _ _ _, hm,
    finishInstr_load1 rfl rfl rfl hrw rfl hlv hfi⟩

/-- The branches (positions 5, 8, 9): registers unchanged. -/
theorem step_br (hpc : t.st.st.2 = pcA 5 ∨ t.st.st.2 = pcA 8 ∨ t.st.st.2 = pcA 9) :
    oc.thread.rview = t.rview ∧ oc.thread.wview = t.wview := by
  obtain ⟨tree, st, c', hex, hr, hfi, hm⟩ := stepOne_fi Arch.armv8 hs ho
  rcases hpc with hpc | hpc | hpc
  · rw [deps_5 _ (hS.st.at (by decide) (by decide) hpc)] at hfi; exact finishInstr_regs_nil rfl rfl rfl hfi
  · rw [deps_8 _ (hS.st.at (by decide) (by decide) hpc)] at hfi; exact finishInstr_regs_nil rfl rfl rfl hfi
  · rw [deps_9 _ (hS.st.at (by decide) (by decide) hpc)] at hfi; exact finishInstr_regs_nil rfl rfl rfl hfi

end Steps

/-- No cell of the worker performs a load exclusive. -/
theorem noXcl {t : Thread isa} (hS : SInv l c t.st) : ∀ tree, isa.exec t.st = some tree → tree.NoXclLoad := by
  intro tree hex
  obtain ⟨hSt, p, hp, hpc, -⟩ := hS
  simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [exec_mov3 _ (hSt.at (by decide) (by decide) hpc)] at hex; cases hex; trivial
  · rw [exec_mov2 _ (hSt.at (by decide) (by decide) hpc)] at hex; cases hex; trivial
  · rw [exec_casa _ (hSt.at (by decide) (by decide) hpc) hSt.x0 hSt.dl] at hex; cases hex; exact fun _ => trivial
  · rw [exec_cbz _ (hSt.at (by decide) (by decide) hpc)] at hex; cases hex; trivial
  · rw [exec_ldr_l _ (hSt.at (by decide) (by decide) hpc) hSt.x0 hSt.dl] at hex; cases hex
    exact ⟨rfl, fun _ => trivial⟩
  · rw [exec_cbnz _ (hSt.at (by decide) (by decide) hpc)] at hex; cases hex; trivial
  · rw [exec_b_try _ (hSt.at (by decide) (by decide) hpc)] at hex; cases hex; trivial
  · rw [exec_ldr_c _ (hSt.at (by decide) (by decide) hpc) hSt.x1 hSt.dc] at hex; cases hex
    exact ⟨rfl, fun _ => trivial⟩
  · rw [exec_add5 _ (hSt.at (by decide) (by decide) hpc)] at hex; cases hex; trivial
  · rw [exec_str_c _ (hSt.at (by decide) (by decide) hpc) hSt.x1 hSt.dc] at hex; cases hex; exact fun _ => trivial
  · rw [exec_stlr _ (hSt.at (by decide) (by decide) hpc) hSt.x0 hSt.dl] at hex; cases hex; exact fun _ => trivial
  · rw [exec_b_done _ (hSt.at (by decide) (by decide) hpc)] at hex; cases hex; trivial
  · have := stepOne_end hSt hpc Arch.armv8 0 default
    simp [stepOne, hex] at this

/-! ## The loop: a long run has a repetition -/

section Loop

variable {s0 : Thread isa} {mem : Memory}

/-- The dominated contexts of two loop states with grown views. -/
theorem ctx_dom {q t : Thread isa} (hq : LInv l c s0 mem q) (ht : LInv l c s0 mem t) (hg : q.views.Grow t.views) :
    (ctx0 tid q mem).Dom (ctx0 tid t mem) :=
  ⟨hg.dom (hq.fwd.trans ht.fwd.symm) (hq.xclb.trans ht.xclb.symm), hq.prom.trans ht.prom.symm, rfl, .nil,
   Nat.le_refl _, rfl, rfl⟩

/-- **The cut at a second `MOV`-reached `CASA` cell**: `q` (reached in `a₁`
steps) dominates the current `t`. -/
theorem cut_4 {a₁ n : Nat} {q t : Thread isa} {r : Thread isa × Memory}
    (hq : ThreadNPn Arch.armv8 tid a₁ (s0, mem) (q, mem)) (hqi : LInv l c s0 mem q)
    (hqst : q.st = goto s0.st { s0.st.st.1 with regs := s0.st.st.1.regs.setXReg .X2 0#64 } (pcA 4))
    (hqr : q.rview = s0.rview.setIfInBounds 2 0) (hqw : q.wview = s0.wview.setIfInBounds 2 0)
    (hg : q.views.Grow t.views) (ht : LInv l c s0 mem t)
    (hst : t.st = goto s0.st { s0.st.st.1 with regs := s0.st.st.1.regs.setXReg .X2 0#64 } (pcA 4))
    (hrv : t.rview = s0.rview.setIfInBounds 2 0) (hwv : t.wview = s0.wview.setIfInBounds 2 0)
    (hrun : ThreadNPn Arch.armv8 tid n (t, mem) r) (hp : r.1.prom = []) :
    ∃ m, m ≤ a₁ + n ∧ CertOkN Arch.armv8 tid s0 mem m := by
  have hd : q.Dom t := ⟨hqst.trans hst.symm, by rw [hqr, hrv]; exact ArrLe.refl _, by rw [hqw, hwv]; exact ArrLe.refl _,
    hg.dom (hqi.fwd.trans ht.fwd.symm) (hqi.xclb.trans ht.xclb.symm), hqi.prom.trans ht.prom.symm⟩
  obtain ⟨r', hr', hdr, -⟩ := hrun.dom (q, mem) hd rfl
  exact ⟨a₁ + n, Nat.le_refl _, r'.1, r'.2, hq.trans hr', hdr.prom.trans hp⟩

/-- **The cut at a second `LDR` step**: the later read (from `t`) replays
from the earlier `LDR` state `q`. -/
theorem cut_7 {a₁ n : Nat} {q t : Thread isa} {oc : Outcome isa} {r : Thread isa × Memory}
    (hq : ThreadNPn Arch.armv8 tid a₁ (s0, mem) (q, mem)) (hqi : LInv l c s0 mem q) (hqpc : q.st.st.2 = pcA 7)
    (hg : q.views.Grow t.views) (ht : LInv l c s0 mem t) (hpc : t.st.st.2 = pcA 7)
    {outs : List (Except String (Outcome isa))} (hs : stepOne Arch.armv8 t tid mem = some outs) (ho : .ok oc ∈ outs)
    (hrun : ThreadNPn Arch.armv8 tid n (oc.thread, oc.mem) r) (hp : r.1.prom = []) :
    ∃ m, m ≤ a₁ + 1 + n ∧ CertOkN Arch.armv8 tid s0 mem m := by
  obtain ⟨ts, v, c', ν, hx, hlv, hcm, hcp, hm, hoc⟩ := step_7 ht.sinv hs ho hpc
  have hiv : (instrViews q { addrRegs := [.x 0], loadDefs := [.x 2] }).Dom
      (instrViews t { addrRegs := [.x 0], loadDefs := [.x 2] }) := by
    rw [instrViews_7, instrViews_7, hqi.rv.get0, ht.rv.get0, hqi.wv.get0, ht.wv.get0]; exact .refl _
  obtain ⟨c₂, hx₂, hd₂⟩ := readSuccs_dom Arch.armv8 hiv (ctx_dom hqi ht hg) hx
  obtain ⟨t', v', hxe, -, -, -, -⟩ := (mem_readSuccs Arch.armv8).mp hx₂
  simp only [Prod.mk.injEq] at hxe
  obtain ⟨rfl, rfl, hc₂⟩ := hxe
  have hat := hqi.sinv.st.at (by decide) (by decide) hqpc
  have hex := exec_ldr_l _ hat hqi.sinv.st.x0 hqi.sinv.st.dl
  have hr : .ok (goto q.st { q.st.st.1 with regs := q.st.st.1.regs.setXReg .X2 (BitVec.setWidth 64
      (BitVec.setWidth 32 v)) } (pcA 8), c₂) ∈
      runTree Arch.armv8 tid (instrViews q (isa.deps q.st)) (ctx0 tid q mem) (.load .plain false (L4 l) fun v =>
        .done (goto q.st { q.st.st.1 with regs := q.st.st.1.regs.setXReg .X2 (BitVec.setWidth 64
          (BitVec.setWidth 32 v)) } (pcA 8))) := by
    rw [deps_7 _ hat]
    simp only [runTree, List.mem_flatMap]
    exact ⟨_, hx₂, run_done_exists Arch.armv8 tid (instrViews q { addrRegs := [.x 0], loadDefs := [.x 2] }) _ _⟩
  obtain ⟨ν₂, hlv₂⟩ : ∃ ν₂, c₂.loadViews = [ν₂] := ⟨_, by rw [hc₂, readNext_loadViews]; rfl⟩
  have hth' : ∃ th : Thread isa, th = ({ q with
      st := goto q.st { q.st.st.1 with regs := q.st.st.1.regs.setXReg .X2 (BitVec.setWidth 64
        (BitVec.setWidth 32 v)) } (pcA 8)
      views := c₂.views
      prom := c₂.prom } : Thread isa).setRegView (.x 2) ν₂ ν₂ := ⟨_, rfl⟩
  obtain ⟨th, hth⟩ := hth'
  have hrw₂ : c₂.rmwWrote = false := by rw [hc₂, readNext_rmwWrote]
  have hcm₂ : c₂.mem = mem := by rw [hc₂, readNext_mem]
  have hfi : th ∈ finishInstr q (isa.deps q.st) (instrViews q (isa.deps q.st))
      (goto q.st { q.st.st.1 with regs := q.st.st.1.regs.setXReg .X2 (BitVec.setWidth 64 (BitVec.setWidth 32 v)) }
        (pcA 8)) c₂ := by
    rw [deps_7 _ hat]
    unfold finishInstr
    simp only [hlv₂, hrw₂, List.foldl_nil, List.foldl_cons, List.length_singleton, Bool.and_false,
      Bool.false_eq_true, ↓reduceIte, List.mem_singleton]
    rw [hth]
    try rfl
  obtain ⟨outs', hs', ho'⟩ := stepOne_of_fi Arch.armv8 hex hr hfi
  -- the replayed thread dominates the thread after the later read
  have hν : ν₂ ≤ ν := by
    have := hd₂.loadViews
    rw [hlv, hlv₂] at this
    cases this with
    | cons h1 h2 => exact h1
  have hd : th.Dom oc.thread := by
    rw [hoc, hth]
    refine ⟨?_, ?_, ?_, hd₂.views, hd₂.prom⟩
    · show goto q.st _ _ = goto t.st _ _
      rw [hqi.core.set, ht.core.set]
    · show ArrLe (q.rview.set! 2 _) (t.rview.set! 2 ν)
      simp only [Array.set!_eq_setIfInBounds]
      rw [hqi.rv.set, ht.rv.set]
      exact (ArrLe.refl _).setIfInBounds 2 hν
    · show ArrLe (q.wview.set! 2 _) (t.wview.set! 2 ν)
      simp only [Array.set!_eq_setIfInBounds]
      rw [hqi.wv.set, ht.wv.set]
      exact (ArrLe.refl _).setIfInBounds 2 hν
  rw [hm] at hrun
  obtain ⟨r', hr', hdr, -⟩ := hrun.dom (th, mem) hd rfl
  refine ⟨a₁ + 1 + n, Nat.le_refl _, r'.1, r'.2, ?_, hdr.prom.trans hp⟩
  exact (hq.tail ⟨outs', _, hs', ho', by rw [hcm₂]⟩).trans hr'

/-- **A write-free loop run is bounded by `Φ`, or a shorter certification
exists**: induction along the run, carrying the prefix length `a` and the
witnesses of the two repetitions. -/
theorem loop_bound : ∀ (n : Nat) (p r : Thread isa × Memory), ThreadRun Arch.armv8 tid n p r → r.1.prom = [] →
    p.2 = mem → ∀ (a : Nat) (h7 h4 : Bool), ThreadNPn Arch.armv8 tid a (s0, mem) p → LInv l c s0 mem p.1 →
    (h7 = true → W7 l c tid s0 mem a p.1) → (h4 = true → W4 l c tid s0 mem a p.1) →
    (∀ i ∈ [3, 4, 5, 7, 8, 9], p.1.st.st.2 = pcA i → n ≤ Φ i h7 h4) ∨
      ∃ m, m < a + n ∧ CertOkN Arch.armv8 tid s0 mem m := by
  intro n p r h
  induction h with
  | refl p => intro _ _ _ _ _ _ _ _ _; exact .inl fun _ _ _ => Nat.zero_le _
  | @step n p q r hs rest ih =>
    intro hp hpm a h7 h4 hpre hI hW7 hW4
    obtain ⟨t, mem'⟩ := p
    simp only at hpm hI hW7 hW4 hpre
    subst mem'
    obtain ⟨outs, oc, hs, ho, rfl⟩ := hs
    obtain ⟨i, hi, hpc⟩ := hI.pos
    have hpos : ∀ j ∈ [3, 4, 5, 7, 8, 9], t.st.st.2 = pcA j → j = i := fun j hj hj' =>
      addrOf_inj (by simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega)
        (by simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega) (hj'.symm.trans hpc)
    obtain ⟨hS', hg, hx', hfw⟩ := step_gen hI.sinv hs ho (noXcl hI.sinv) hI.xclb
    -- the witnesses' views grow with the step
    have hW7' : h7 = true → W7 l c tid s0 mem (a + 1) oc.thread := fun h =>
      let ⟨q, a₁, ha, hq, hqi, hqpc, hgq⟩ := hW7 h; ⟨q, a₁, by omega, hq, hqi, hqpc, hgq.trans hg⟩
    have hW4' : h4 = true → W4 l c tid s0 mem (a + 1) oc.thread := fun h =>
      let ⟨q, a₁, ha, hq, hqi, hqst, hqr, hqw, hgq⟩ := hW4 h; ⟨q, a₁, by omega, hq, hqi, hqst, hqr, hqw, hgq.trans hg⟩
    have hpre' : ThreadNPn Arch.armv8 tid (a + 1) (s0, mem) (oc.thread, oc.mem) := hpre.tail ⟨outs, oc, hs, ho, rfl⟩
    have hpre'' : ∀ hm : oc.mem = mem, ThreadNPn Arch.armv8 tid (a + 1) (s0, mem) (oc.thread, mem) := fun hm => by
      have e : (oc.thread, mem) = (oc.thread, oc.mem) := by rw [hm]
      rw [e]; exact hpre'
    -- a loop invariant for the next state from the generic facts
    have mk : ∀ (j : Nat), j ∈ [3, 4, 5, 7, 8, 9] → oc.thread.st.st.2 = pcA j → oc.mem = mem →
        oc.thread.prom = t.prom → Core s0.st oc.thread.st → RegX2 s0.rview oc.thread.rview →
        RegX2 s0.wview oc.thread.wview → LInv l c s0 mem oc.thread := fun j hj hjpc hm hpr hc hr hw =>
      ⟨⟨j, hj, hjpc⟩, hS', hc, hr, hw, hI.grow.trans hg, (hfw hm hpr).trans hI.fwd, hx', hpr.trans hI.prom⟩
    -- the bound for the current cell from the bound for the next
    have bnd : ∀ (j : Nat), j ∈ [3, 4, 5, 7, 8, 9] → oc.thread.st.st.2 = pcA j → ∀ (h7' h4' : Bool),
        (∀ k ∈ [3, 4, 5, 7, 8, 9], oc.thread.st.st.2 = pcA k → n ≤ Φ k h7' h4') → n + 1 ≤ Φ j h7' h4' + 1 :=
      fun j hj hjpc _ _ hb => Nat.succ_le_succ (hb j hj hjpc)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    · -- 3: `mov w2,#0`
      obtain ⟨hm, hoc⟩ := step_3 hI.sinv hs ho hpc
      have hst : oc.thread.st = goto s0.st { s0.st.st.1 with regs := s0.st.st.1.regs.setXReg .X2 0#64 } (pcA 4) := by
        rw [hoc]; exact hI.core.set _ _
      have hrv : oc.thread.rview = s0.rview.setIfInBounds 2 0 := by
        rw [hoc]; exact hI.rv.set 0
      have hwv : oc.thread.wview = s0.wview.setIfInBounds 2 0 := by
        rw [hoc]; exact hI.wv.set 0
      have hI' : LInv l c s0 mem oc.thread := mk 4 (by decide) (by rw [hst]) hm (by rw [hoc]; rfl) ⟨_, _, hst⟩
        (.inr ⟨_, hrv⟩) (.inr ⟨_, hwv⟩)
      cases h4 with
      | true =>
        have e : (oc.thread, mem) = (oc.thread, oc.mem) := by rw [hm]
        obtain ⟨q, a₁, ha, hq, hqi, hqst, hqr, hqw, hgq⟩ := hW4 rfl
        obtain ⟨m, hm', hc⟩ := cut_4 hq hqi hqst hqr hqw (hgq.trans hg) hI' hst hrv hwv (by rw [e]; exact rest.toNPn) hp
        exact .inr ⟨m, by omega, hc⟩
      | false =>
        have hW4'' : W4 l c tid s0 mem (a + 1) oc.thread :=
          ⟨oc.thread, a + 1, Nat.le_refl _, hpre'' hm, hI', hst, hrv, hwv, Views.Grow.refl _⟩
        rcases ih hp hm (a + 1) h7 true hpre' hI' hW7' (fun _ => hW4'') with hb | ⟨m, hm', hc⟩
        · refine .inl fun j hj hj' => ?_
          obtain rfl := hpos j hj hj'
          have := bnd 4 (by decide) (by rw [hst]) h7 true hb
          cases h7 <;> simp only [Φ] at this ⊢ <;> omega
        · exact .inr ⟨m, by omega, hc⟩
    · -- 4: `casa`
      have hz : w32 t.st.st.1.regs.X2 = 0#32 := by
        obtain ⟨j, hj, hj', hI4⟩ := hI.sinv.pc
        obtain rfl : j = 4 := addrOf_inj hj (by decide) (hj'.symm.trans hpc)
        exact hI4.2 rfl
      rcases step_4 hI.sinv hs ho hpc hz with ⟨tr, old, c', ν, hx, hlv, hcm, hcp, hm, hoc⟩ | ⟨hpc5, hz⟩
      · -- failing: to position 5 with `X2 ≠ 0`
        have hI' : LInv l c s0 mem oc.thread := mk 5 (by decide) (by rw [hoc]; rfl) hm (by rw [hoc]; exact hcp)
          (by rw [hoc]; exact hI.core.set' _ _) (by rw [hoc]; exact hI.rv.set' ν) (by rw [hoc]; exact hI.wv.set' ν)
        rcases ih hp hm (a + 1) h7 h4 hpre' hI' hW7' hW4' with hb | ⟨m, hm', hc⟩
        · refine .inl fun j hj hj' => ?_
          obtain rfl := hpos j hj hj'
          have := bnd 5 (by decide) (by rw [hoc]; rfl) h7 h4 hb
          cases h7 <;> cases h4 <;> simp only [Φ] at this ⊢ <;> omega
        · exact .inr ⟨m, by omega, hc⟩
      · -- succeeding: the tail
        have := tail_bound n _ r rest hS' 5 (by decide) hpc5 (fun _ => hz)
        refine .inl fun j hj hj' => ?_
        obtain rfl := hpos j hj hj'
        cases h7 <;> cases h4 <;> simp only [Φ, Ψ] at this ⊢ <;> omega
    · -- 5: `cbz`
      obtain ⟨hm, hst, hpr, -⟩ := s5 hI.sinv.st hs ho hpc
      obtain ⟨hrv, hwv⟩ := step_br hI.sinv hs ho (.inl hpc)
      by_cases hz : w32 t.st.st.1.regs.X2 = 0#32
      · rw [ite_eq_left hz] at hst
        have := tail_bound n _ r rest hS' 11 (by decide) (by rw [hst]) (fun h => absurd h (by decide))
        refine .inl fun j hj hj' => ?_
        obtain rfl := hpos j hj hj'
        cases h7 <;> cases h4 <;> simp only [Φ, Ψ] at this ⊢ <;> omega
      · rw [ite_eq_right hz] at hst
        have hI' : LInv l c s0 mem oc.thread := mk 7 (by decide) (by rw [hst]) hm hpr (by rw [hst]; exact hI.core.goto _)
          (hrv ▸ hI.rv) (hwv ▸ hI.wv)
        rcases ih hp hm (a + 1) h7 h4 hpre' hI' hW7' hW4' with hb | ⟨m, hm', hc⟩
        · refine .inl fun j hj hj' => ?_
          obtain rfl := hpos j hj hj'
          have := bnd 7 (by decide) (by rw [hst]) h7 h4 hb
          cases h7 <;> cases h4 <;> simp only [Φ] at this ⊢ <;> omega
        · exact .inr ⟨m, by omega, hc⟩
    · -- 7: `ldr w2,[x0]`
      cases h7 with
      | true =>
        obtain ⟨q, a₁, ha, hq, hqi, hqpc, hgq⟩ := hW7 rfl
        obtain ⟨m, hm', hc⟩ := cut_7 hq hqi hqpc hgq hI hpc hs ho rest.toNPn hp
        exact .inr ⟨m, by omega, hc⟩
      | false =>
        obtain ⟨ts, v, c', ν, hx, hlv, hcm, hcp, hm, hoc⟩ := step_7 hI.sinv hs ho hpc
        have hI' : LInv l c s0 mem oc.thread := mk 8 (by decide) (by rw [hoc]; rfl) hm (by rw [hoc]; exact hcp)
          (by rw [hoc]; exact hI.core.set' _ _) (by rw [hoc]; exact hI.rv.set' ν) (by rw [hoc]; exact hI.wv.set' ν)
        have hW7'' : W7 l c tid s0 mem (a + 1) oc.thread := ⟨t, a, Nat.lt_succ_self _, hpre, hI, hpc, hg⟩
        rcases ih hp hm (a + 1) true h4 hpre' hI' (fun _ => hW7'') hW4' with hb | ⟨m, hm', hc⟩
        · refine .inl fun j hj hj' => ?_
          obtain rfl := hpos j hj hj'
          have := bnd 8 (by decide) (by rw [hoc]; rfl) true h4 hb
          cases h4 <;> simp only [Φ] at this ⊢ <;> omega
        · exact .inr ⟨m, by omega, hc⟩
    · -- 8: `cbnz`
      obtain ⟨hm, hst, hpr, -⟩ := s8 hI.sinv.st hs ho hpc
      obtain ⟨hrv, hwv⟩ := step_br hI.sinv hs ho (.inr (.inl hpc))
      by_cases hz : w32 t.st.st.1.regs.X2 = 0#32
      · rw [ite_eq_left hz] at hst
        have hI' : LInv l c s0 mem oc.thread := mk 9 (by decide) (by rw [hst]) hm hpr (by rw [hst]; exact hI.core.goto _)
          (hrv ▸ hI.rv) (hwv ▸ hI.wv)
        rcases ih hp hm (a + 1) h7 h4 hpre' hI' hW7' hW4' with hb | ⟨m, hm', hc⟩
        · refine .inl fun j hj hj' => ?_
          obtain rfl := hpos j hj hj'
          have := bnd 9 (by decide) (by rw [hst]) h7 h4 hb
          cases h7 <;> cases h4 <;> simp only [Φ] at this ⊢ <;> omega
        · exact .inr ⟨m, by omega, hc⟩
      · rw [ite_eq_right hz] at hst
        have hI' : LInv l c s0 mem oc.thread := mk 7 (by decide) (by rw [hst]) hm hpr (by rw [hst]; exact hI.core.goto _)
          (hrv ▸ hI.rv) (hwv ▸ hI.wv)
        rcases ih hp hm (a + 1) h7 h4 hpre' hI' hW7' hW4' with hb | ⟨m, hm', hc⟩
        · refine .inl fun j hj hj' => ?_
          obtain rfl := hpos j hj hj'
          have := bnd 7 (by decide) (by rw [hst]) h7 h4 hb
          cases h7 <;> cases h4 <;> simp only [Φ] at this ⊢ <;> omega
        · exact .inr ⟨m, by omega, hc⟩
    · -- 9: `b try`
      obtain ⟨hm, hst, hpr, -⟩ := s9 hI.sinv.st hs ho hpc
      obtain ⟨hrv, hwv⟩ := step_br hI.sinv hs ho (.inr (.inr hpc))
      have hI' : LInv l c s0 mem oc.thread := mk 3 (by decide) (by rw [hst]) hm hpr (by rw [hst]; exact hI.core.goto _)
        (hrv ▸ hI.rv) (hwv ▸ hI.wv)
      rcases ih hp hm (a + 1) h7 h4 hpre' hI' hW7' hW4' with hb | ⟨m, hm', hc⟩
      · refine .inl fun j hj hj' => ?_
        obtain rfl := hpos j hj hj'
        have := bnd 3 (by decide) (by rw [hst]) h7 h4 hb
        cases h7 <;> cases h4 <;> simp only [Φ] at this ⊢ <;> omega
      · exact .inr ⟨m, by omega, hc⟩

end Loop

/-! ## The bound -/

/-- `LInv` of a loop state relative to itself. -/
theorem linv_self {t : Thread isa} (hS : SInv l c t.st) (hx : t.views.xclb = none) {i : Nat}
    (hi : i ∈ [3, 4, 5, 7, 8, 9]) (hpc : t.st.st.2 = pcA i) (mem : Memory) : LInv l c t mem t :=
  ⟨⟨i, hi, hpc⟩, hS, Core.self _, .inl rfl, .inl rfl, Views.Grow.refl _, rfl, hx, rfl⟩

/-- **Every certification of a worker is within `13` instructions.** -/
theorem certOkN_bound {t : Thread isa} {mem : Memory} (hS : SInv l c t.st) (hx : t.views.xclb = none) {n : Nat}
    (h : CertOkN Arch.armv8 tid t mem n) : CertOkN Arch.armv8 tid t mem 13 := by
  refine CertOkN.bound_of_shorter 13 (fun n r hr hp hn => ?_) h
  obtain ⟨hSt, i, hi, hpc, -⟩ := id hS
  have loop : ∀ (s0 : Thread isa) (j : Nat), j ∈ [3, 4, 5, 7, 8, 9] → s0.st.st.2 = pcA j →
      SInv l c s0.st → s0.views.xclb = none → ∀ (k : Nat) (r : Thread isa × Memory),
      ThreadRun Arch.armv8 tid k (s0, mem) r → r.1.prom = [] → Φ j false false < k →
      ∃ m, m < k ∧ CertOkN Arch.armv8 tid s0 mem m := by
    intro s0 j hj hjpc hS0 hx0 k r hr hp hk
    rcases loop_bound k (s0, mem) r hr hp rfl 0 false false (.refl _ _) (linv_self hS0 hx0 hj hjpc mem)
        (fun h => Bool.noConfusion h) (fun h => Bool.noConfusion h) with hb | ⟨m, hm, hc⟩
    · exact absurd (hb j hj hjpc) (Nat.not_le_of_lt hk)
    · exact ⟨m, by omega, hc⟩
  have hlt : ∀ j, Φ j false false < n := fun j => Nat.lt_of_le_of_lt (Φ_le j false false) hn
  simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- `mov w3,#1`: one step, then the loop
    cases hr with
    | refl => omega
    | @step n' _ q _ hs rest =>
      obtain ⟨outs, oc, hs, ho, rfl⟩ := hs
      obtain ⟨hm, hst, -⟩ := SpinCasInv.s1 hSt hs ho hpc
      obtain ⟨hS', -, hx', -⟩ := step_gen hS hs ho (noXcl hS) hx
      rw [hm] at rest
      obtain ⟨m, hm', t', mem', hr', hp'⟩ := loop oc.thread 3 (by decide) (by rw [hst]) hS' hx' n' _ rest hp
        (by simp only [Φ]; omega)
      exact ⟨m + 1, by omega, t', mem', .step ⟨outs, oc, hs, ho, by rw [hm]⟩ hr', hp'⟩
  · exact loop t 3 (by decide) hpc hS hx n r hr hp (hlt 3)
  · exact loop t 4 (by decide) hpc hS hx n r hr hp (hlt 4)
  · by_cases hz : w32 t.st.st.1.regs.X2 = 0#32
    · exact absurd (tail_bound n _ r hr hS 5 (by decide) hpc fun _ => hz) (by simp only [Ψ]; omega)
    · exact loop t 5 (by decide) hpc hS hx n r hr hp (hlt 5)
  · exact loop t 7 (by decide) hpc hS hx n r hr hp (hlt 7)
  · exact loop t 8 (by decide) hpc hS hx n r hr hp (hlt 8)
  · exact loop t 9 (by decide) hpc hS hx n r hr hp (hlt 9)
  all_goals exact absurd (tail_bound n _ r hr hS _ (by decide) hpc (fun h => absurd h (by decide))) (by simp only [Ψ]; omega)

/-! ## Reachable configurations -/

/-- No thread has a pending load exclusive (none of the worker's cells
performs one). -/
def XclbNone (cfg : Config isa) : Prop := ∀ (i : Nat) u, cfg.threads[i]? = some u → u.views.xclb = none

theorem xclbNone_step {fuel : Nat} {cfg cfg' : Config isa} (hI : InvS fuel l c cfg) (h : XclbNone cfg) {tid : Nat}
    (hst : StepSem Arch.armv8 fuel tid cfg cfg') : XclbNone cfg' := by
  rcases hst with ⟨t, outs, oc, ht, hs, ho, -, rfl⟩ | ⟨t, w, ht, -, -, rfl⟩
  · intro i u hu
    rcases wt_get ht hu with ⟨rfl, rfl⟩ | ⟨-, hu⟩
    · have hS := (hI.thr _ t ht).sinv
      exact stepOne_xclb_none Arch.armv8 (stepOne_fi Arch.armv8 hs ho).choose_spec.choose_spec.choose_spec.1
        (noXcl hS _ (stepOne_fi Arch.armv8 hs ho).choose_spec.choose_spec.choose_spec.1) hs ho (h _ t ht)
    · exact h i u hu
  · intro i u hu
    rcases wt_get ht hu with ⟨rfl, rfl⟩ | ⟨-, hu⟩
    · exact h _ t ht
    · exact h i u hu

theorem xclbNone_init (states : List isa.State) (initMem : List (Loc × Val)) :
    XclbNone (Config.init states initMem) := by
  intro i u hu
  simp only [Config.init, List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at hu
  obtain ⟨s, -, rfl⟩ := hu
  rfl

/-- **Bounded certification from every start configuration**: `F = 13`. -/
theorem cas_certBounded {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : Spin.CasStart l c states initMem) : CertBoundedFrom Arch.armv8 (Config.init states initMem) 13 := by
  intro fuel cfg hr tid t n ht hc
  have hinv := NoStuck.reachableSem_inv (fun cfg => InvS fuel l c cfg ∧ XclbNone cfg)
    (fun tid cfg cfg' ⟨hI, hX⟩ hst => by
      obtain ⟨t, ht⟩ : ∃ t, cfg.threads[tid]? = some t := by
        rcases hst with ⟨t, -, -, ht, -⟩ | ⟨t, -, ht, -⟩ <;> exact ⟨t, ht⟩
      exact ⟨inv_step hI ht hst, xclbNone_step hI hX hst⟩) hr ⟨inv_init hs, xclbNone_init _ _⟩
  exact certOkN_bound (hinv.1.thr tid t ht).sinv (hinv.2 tid t ht) hc

/-! ## The fuel-free theorems -/

/-- `SpinSem.CasSpinLiveSem` on the fuel-free semantic machine. -/
def CasSpinLiveSemU : Prop :=
  ∀ l c states initMem, Spin.CasStart l c states initMem →
    ProgressFromSemU Arch.armv8 (Config.init states initMem)
      (fun cfg => WeakFairSemU Arch.armv8 cfg ∧ MemFair Arch.armv8 cfg) Spin.CasWaiting Spin.CasDone

/-- `SpinSem.CasSpinLiveOneShotSem` on the fuel-free semantic machine. -/
def CasSpinLiveOneShotSemU : Prop :=
  ∀ l c states initMem, Spin.CasStart l c states initMem →
    LiveFromSemU Arch.armv8 (Config.init states initMem)
      (fun cfg => WeakFairSemU Arch.armv8 cfg ∧ MemFair Arch.armv8 cfg) Spin.CasWaiting Spin.CasDone

/-- **Deadlock-freedom of the CAS spinlock, fuel-free**: `spin_cas_live_sem`
at fuel `13` through `progressTransfer`. -/
theorem spin_cas_live_semU : CasSpinLiveSemU := fun l c states initMem hs =>
  progressTransfer (cas_certBounded hs) (SpinSemCas.spin_cas_live_sem 13 l c states initMem hs)

/-- **Per-thread liveness of the one-shot CAS workers, fuel-free.** -/
theorem spin_cas_live_oneShot_semU : CasSpinLiveOneShotSemU := fun l c states initMem hs =>
  liveTransfer (cas_certBounded hs) (SpinSemCas.spin_cas_live_oneShot_sem 13 l c states initMem hs)

/-- `spin_cas_live_semU` at the concrete layout `SpinCasPF.casLayout`. -/
theorem spin_cas_live_semU_concrete : @CasSpinLiveSemU SpinCasPF.casLayout :=
  @spin_cas_live_semU SpinCasPF.casLayout SpinCasPF.casValid

/-- `spin_cas_live_oneShot_semU` at the concrete layout. -/
theorem spin_cas_live_oneShot_semU_concrete : @CasSpinLiveOneShotSemU SpinCasPF.casLayout :=
  @spin_cas_live_oneShot_semU SpinCasPF.casLayout SpinCasPF.casValid

end Kraken.Promising.Live.CertBoundedSpinCas
