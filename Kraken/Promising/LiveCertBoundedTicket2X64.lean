/-
**Bounded certification for the x64 ticketlock2**
(`tk2ImageV`, unlocked `incl (owner)` release, valid layout, `Arch.tso`):
`CertBoundedFrom Arch.tso c0 10` for every `Ticket2X64.Tk2StartX`
configuration, and the fuel-free liveness theorem `ticket2_x64_live_semU`
(with `_concrete`).

The proof is `LiveCertBoundedTicketX64` (ticketlock3) at the
ticketlock2 image, cell for cell; the image-independent helpers (`cmpX`,
`Core`, the dependency tactic, `XclbNone`) come from `LiveCertCutX64`. A
certifying solo run of a worker goes `movl $1,%eax` (position 1),
`lock xaddl` (2), then the spin loop `movl (owner),%ecx` / `cmpl %eax,%ecx` /
`jne spin` (4, 5, 6), then the straight line 7–11 to the end (at most `5`
instructions; the release `incl (owner)` at 10 is one instruction with a load
and a store). The `lock xaddl` takes the ticket unconditionally, so the loop
is read-only: along it (*the stretch*) memory and promises are constant, only
`%rcx`, the flags and their register views (slots `2` and `16`) change, and
the scalar views grow. `%eax` (the ticket) is fixed.

If the stretch's promise set is empty, its start is a certification of
length `0`. Otherwise the run cannot end inside the stretch, and **two loads
of `owner`** in it shorten it: the later read replays from the earlier load
state `q` with lower views (`readSuccs_dom`), and so does the following
`cmpl`; the thread after the replayed `cmpl` dominates the thread after the
later one (`cut_4`), then `ThreadNPn.dom` replays the rest.

A run without the repetition is at most `10` instructions long (the
potential `Φ`: `2` before the loop, `3` in it, `5` after it). `F` depends on
the program only.

Names: `exec_cmpX`, `exec_ldoX`, `LInv`, `W4`, `Φ`, `Ψ`, `tail_bound`,
`cut_4`, `loop_bound`, `certOkN_bound`, `ticket2_x64_certBounded`,
`Ticket2X64LiveSemU`, `ticket2_x64_live_semU`, `ticket2_x64_live_semU_concrete`.
-/
import Kraken.Promising.LiveCertBounded
import Kraken.Promising.LiveCertCutRegS
import Kraken.Promising.LiveCertCutX64
import Kraken.Promising.LiveSpinStep
import Kraken.Promising.LiveX64Sem2Ticket

namespace Kraken.Promising.Live.CertBoundedTicket2X64

set_option linter.unusedSectionVars false

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Live
open Kraken.Promising.Live.Ticket2X64Trees Kraken.Promising.Live.TicketStep
open Kraken.Promising.Live.Sem Kraken.Promising.Live.SemShape
open Kraken.Promising.Live.X64Sem2Step Kraken.Promising.Live.X64Sem2Inv
open Kraken.Promising.Live.CertBounded Kraken.Promising.Live.CertCut Kraken.Promising.Live.CertCutX64
open Kraken.Promising.Live.Ticket2X64Inv (Static stepOne_end)
open Kraken.Promising.X64.EnvG.TicketX2 (tk2ImageV tk2WorkerV symTk2)

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout tk2ImageV)]

set_option hygiene false in
local notation "pcA" => (layout tk2ImageV).addrOf

/-! ## The loop cells -/

/-- `cmpl %eax,%ecx` (position 5) with its flags explicit. -/
theorem exec_cmpX (st : State) (h : At st 5) :
    isa.exec st = some (.done (goto st { st.st.1 with status := cmpX st.st.1.regs } (pcA 6))) := by
  rw [show pcA 6 = st.st.2 + .ofNat (Kraken.Layout.size Directive 5) by
    rw [h.pc]; exact addrOf_step (by decide)]
  x64cell h 5 tk2ImageV [tk2ImageV, tk2WorkerV] [label_spin, label_done]
  rfl

/-- `movl (owner),%ecx` (position 4) with its machine data explicit. -/
theorem exec_ldoX (st : State) (h : At st 4) (hdm : Mem.loadInt st.st.1.dmem (symTk2 "owner") 4 = none) :
    isa.exec st = some (.load .plain false ⟨symTk2 "owner", 4⟩ fun v => .done (goto st
      { st.st.1 with regs := st.st.1.regs.set64 .rcx (BitVec.setWidth 64 (BitVec.setWidth 32 v)) } (pcA 5))) := by
  rw [show pcA 5 = st.st.2 + .ofNat (Kraken.Layout.size Directive 4) by
    rw [h.pc]; exact addrOf_step (by decide)]
  x64cell h 4 tk2ImageV [tk2ImageV, tk2WorkerV] [label_spin, label_done, hdm, symTk2]

/-- The loop cells' dependencies: `movl (owner),%ecx`, `cmpl %eax,%ecx`, `jne spin`. -/
theorem deps_4 (st : State) (h : At st 4) : isa.deps st = { loadDefs := [.r .rcx] } := by
  x64depsAt h 4 tk2ImageV [tk2ImageV, tk2WorkerV]
theorem deps_5 (st : State) (h : At st 5) :
    isa.deps st = { dataRegs := [.r .rcx, .r .rax], defs := [.rflags] } := by
  x64depsAt h 5 tk2ImageV [tk2ImageV, tk2WorkerV]
theorem deps_6 (st : State) (h : At st 6) : isa.deps st = { condRegs := [.rflags], isBranch := true } := by
  x64depsAt h 6 tk2ImageV [tk2ImageV, tk2WorkerV]

/-! ## The loop invariant and the witness -/

variable {tid : Nat}

/-- **The loop invariant**, relative to the thread `s0` at the start of the
stretch: a loop cell, `SInv`, `Core`, only slots `2` (`%rcx`) and `16` (the
flags) of the register views changed, scalar views grown, the forwarding table
and promises unchanged, no pending load exclusive. -/
structure LInv (s0 t : Thread isa) : Prop where
  pos : ∃ i ∈ [4, 5, 6], t.st.st.2 = pcA i
  sinv : SInv t.st
  core : Core s0.st t.st
  rv : RegS 2 16 s0.rview t.rview
  wv : RegS 2 16 s0.wview t.wview
  grow : s0.views.Grow t.views
  fwd : t.views.fwdb = s0.views.fwdb
  xclb : t.views.xclb = none
  prom : t.prom = s0.prom

/-- An earlier load state `q` (reached in `a₁ < a` steps), with views grown
up to the current thread. -/
def W4 (tid : Nat) (s0 : Thread isa) (mem : Memory) (a : Nat) (cur : Thread isa) : Prop :=
  ∃ (q : Thread isa) (a₁ : Nat), a₁ < a ∧ ThreadNPn Arch.tso tid a₁ (s0, mem) (q, mem) ∧ LInv s0 q ∧
    q.st.st.2 = pcA 4 ∧ q.views.Grow cur.views

/-- **The potential**: the longest run without a repetition from a loop cell,
given whether a load step has been seen in the stretch. -/
def Φ : Nat → Bool → Nat
  | 4, false => 8 | 5, false => 10 | 6, false => 9
  | 5, true => 7 | 6, true => 6
  | _, _ => 0

omit hv in
theorem Φ_le (i : Nat) (h : Bool) : Φ i h ≤ 10 := by
  unfold Φ; split <;> omega

/-! ## The straight line after the loop -/

/-- The remaining steps from the critical section on. -/
def Ψ : Nat → Nat
  | 7 => 5 | 8 => 4 | 9 => 3 | 10 => 2 | 11 => 1 | _ => 0

/-- **The tail**: from position 7 on, a solo run has at most `Ψ i ≤ 5`
instructions. -/
theorem tail_bound : ∀ (n : Nat) (p r : Thread isa × Memory), ThreadRun Arch.tso tid n p r → SInv p.1.st →
    ∀ i ∈ [7, 8, 9, 10, 11, 13], p.1.st.st.2 = pcA i → n ≤ Ψ i := by
  intro n p r h
  induction h with
  | refl p => intro _ i _ _; exact Nat.zero_le _
  | @step n p q r hs _ ih =>
    intro hS i hi hpc
    obtain ⟨outs, oc, hs, ho, rfl⟩ := hs
    have hS' := (step_sinv hS hs ho).1
    have hit : i ∈ tkPcs := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hn := X64Sem2Ticket.pos_step hS hit hpc hs ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    · have := ih hS' 8 (by decide) hn; simp only [Ψ] at this ⊢; omega
    · have := ih hS' 9 (by decide) hn; simp only [Ψ] at this ⊢; omega
    · have := ih hS' 10 (by decide) hn; simp only [Ψ] at this ⊢; omega
    · have := ih hS' 11 (by decide) hn; simp only [Ψ] at this ⊢; omega
    · have := ih hS' 13 (by decide) hn; simp only [Ψ] at this ⊢; omega
    · rw [stepOne_end hS.st hpc] at hs; cases hs

/-! ## One loop step -/

/-- No cell of the worker performs a load exclusive. -/
theorem noXcl {t : Thread isa} (hS : SInv t.st) : ∀ tree, isa.exec t.st = some tree → tree.NoXclLoad := by
  intro tree hex
  obtain ⟨hSt, p, hp, hpc⟩ := hS
  simp only [tkPcs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨md, -, -, h⟩ := exec_mov1 _ (hSt.at (by decide) (by decide) hpc)
    rw [h] at hex; cases hex; trivial
  · obtain ⟨g, -, h⟩ := exec_xadd _ (hSt.at (by decide) (by decide) hpc) hSt.dx
    rw [h] at hex; cases hex; exact fun _ => trivial
  · rw [exec_ldoX _ (hSt.at (by decide) (by decide) hpc) hSt.dO] at hex; cases hex
    exact ⟨rfl, fun _ => trivial⟩
  · rw [exec_cmpX _ (hSt.at (by decide) (by decide) hpc)] at hex; cases hex; trivial
  · rw [exec_jne _ (hSt.at (by decide) (by decide) hpc)] at hex; cases hex; trivial
  · obtain ⟨g, -, h⟩ := exec_ldc _ (hSt.at (by decide) (by decide) hpc) hSt.dc
    rw [h] at hex; cases hex; exact ⟨rfl, fun _ => trivial⟩
  · obtain ⟨md, -, -, -, h⟩ := exec_addd _ (hSt.at (by decide) (by decide) hpc)
    rw [h] at hex; cases hex; trivial
  · obtain ⟨v, md, -, -, -, h⟩ := exec_stc _ (hSt.at (by decide) (by decide) hpc) hSt.dc
    rw [h] at hex; cases hex; exact fun _ => trivial
  · obtain ⟨g, -, h⟩ := exec_inc _ (hSt.at (by decide) (by decide) hpc) hSt.dO
    rw [h] at hex; cases hex; exact ⟨rfl, fun _ _ => trivial⟩
  · rw [exec_jmp _ (hSt.at (by decide) (by decide) hpc)] at hex; cases hex; trivial
  · have := stepOne_end hSt hpc Arch.tso 0 default
    simp [stepOne, hex] at this

section Steps

variable {t : Thread isa} {mem : Memory} {outs : List (Except String (Outcome isa))} {oc : Outcome isa}
  (hS : SInv t.st) (hs : stepOne Arch.tso t tid mem = some outs) (ho : .ok oc ∈ outs)

include hS hs ho

/-- The generic facts of a step: `SInv`, views grown, no pending exclusive,
and, without a write, forwarding and promises unchanged. -/
theorem step_gen (hx : t.views.xclb = none) :
    SInv oc.thread.st ∧ t.views.Grow oc.thread.views ∧ oc.thread.views.xclb = none ∧
      (oc.mem = mem → oc.thread.prom = t.prom → oc.thread.views.fwdb = t.views.fwdb) := by
  obtain ⟨tree, -, -, hex, -⟩ := stepOne_fi Arch.tso hs ho
  obtain ⟨hg, -, hnw⟩ := stepOne_grow Arch.tso hs ho
  refine ⟨(step_sinv hS hs ho).1, hg, stepOne_xclb_none Arch.tso hex (noXcl hS tree hex) hs ho hx,
    fun hm hp => ?_⟩
  exact ((hnw (by rw [hm])).2 (by rw [hp])).1

/-- `movl (owner),%ecx` (position 4): the read with its context, `%rcx := v`
with the read's post-view. -/
theorem step_4 (hpc : t.st.st.2 = pcA 4) :
    ∃ ts v c' ν, (ts, v, c') ∈ readSuccs Arch.tso (instrViews t { loadDefs := [.r .rcx] })
        (ctx0 tid t mem) .plain false ⟨symTk2 "owner", 4⟩ false ∧
      c'.loadViews = [ν] ∧ c'.mem = mem ∧ c'.prom = t.prom ∧ oc.mem = mem ∧ oc.thread =
      { t with
        st := goto t.st { t.st.st.1 with regs := t.st.st.1.regs.set64 .rcx (BitVec.setWidth 64
          (BitVec.setWidth 32 v)) } (pcA 5)
        views := c'.views
        prom := c'.prom }.setRegView (.r .rcx) ν ν := by
  have hat := hS.st.at (by decide) (by decide) hpc
  obtain ⟨tree, st, c', hex, hr, hfi, hm⟩ := stepOne_fi Arch.tso hs ho
  rw [exec_ldoX _ hat hS.st.dO] at hex
  obtain rfl := Option.some.inj hex
  rw [deps_4 _ hat] at hr hfi
  obtain ⟨ts, v, hx, rfl⟩ := run_load_ctx Arch.tso tid _ hr
  obtain ⟨t', v', hxe, -, -, -, -⟩ := (mem_readSuccs Arch.tso).mp hx
  simp only [Prod.mk.injEq] at hxe
  obtain ⟨rfl, rfl, rfl⟩ := hxe
  have hlv := readNext_loadViews Arch.tso (instrViews t { loadDefs := [.r .rcx] })
    (ctx0 tid t mem) .plain false ⟨symTk2 "owner", 4⟩ false ts v
  have hrw := readNext_rmwWrote Arch.tso (instrViews t { loadDefs := [.r .rcx] })
    (ctx0 tid t mem) .plain false ⟨symTk2 "owner", 4⟩ false ts v
  exact ⟨ts, v, _, _, hx, hlv, readNext_mem _ _ _ _ _ _ _ _ _, readNext_prom _ _ _ _ _ _ _ _ _, hm,
    finishInstr_load1 rfl rfl rfl hrw rfl hlv hfi⟩

/-- `cmpl %eax,%ecx` (position 5): the flags `cmpX`, with the join of
`%rcx`'s and `%rax`'s views. -/
theorem step_5 (hpc : t.st.st.2 = pcA 5) : oc.mem = mem ∧ oc.thread =
    { t with
      st := goto t.st { t.st.st.1 with status := cmpX t.st.st.1.regs } (pcA 6)
      views := t.views
      prom := t.prom }.setRegView .rflags (max (max 0 (max (max 0 (t.rview[2]! : View)) t.rview[0]!)) 0)
        (max (max 0 (max (max 0 (t.wview[2]! : View)) t.wview[0]!)) 0) := by
  have hat := hS.st.at (by decide) (by decide) hpc
  obtain ⟨tree, st, c', hex, hr, hfi, hm⟩ := stepOne_fi Arch.tso hs ho
  rw [exec_cmpX _ hat] at hex
  obtain rfl := Option.some.inj hex
  obtain ⟨rfl, rfl⟩ := run_done Arch.tso tid _ hr
  rw [deps_5 _ hat] at hfi
  have := finishInstr_def1 rfl rfl rfl rfl rfl rfl hfi
  rw [instrViews_cmp] at this
  exact ⟨hm, this⟩

/-- `jne spin` (position 6): register views unchanged. -/
theorem step_6 (hpc : t.st.st.2 = pcA 6) : oc.thread.rview = t.rview ∧ oc.thread.wview = t.wview := by
  obtain ⟨tree, st, c', hex, hr, hfi, hm⟩ := stepOne_fi Arch.tso hs ho
  rw [deps_6 _ (hS.st.at (by decide) (by decide) hpc)] at hfi
  exact finishInstr_regs_nil rfl rfl rfl hfi

end Steps

/-! ## The cut -/

section Loop

variable {s0 : Thread isa} {mem : Memory}

/-- The dominated contexts of two loop states with grown views. -/
theorem ctx_dom {q t : Thread isa} (hq : LInv s0 q) (ht : LInv s0 t) (hg : q.views.Grow t.views) :
    (ctx0 tid q mem).Dom (ctx0 tid t mem) :=
  ⟨hg.dom (hq.fwd.trans ht.fwd.symm) (hq.xclb.trans ht.xclb.symm), hq.prom.trans ht.prom.symm, rfl, .nil,
   Nat.le_refl _, rfl, rfl⟩

/-- **The cut at a second load of `owner`**: the later read (from `t`)
replays from the earlier load state `q`, and so does the following `cmpl`; the
thread after the replayed `cmpl` dominates the thread after the later one. -/
theorem cut_4 {a₁ n : Nat} {q t : Thread isa} {oc : Outcome isa} {r : Thread isa × Memory}
    (hq : ThreadNPn Arch.tso tid a₁ (s0, mem) (q, mem)) (hqi : LInv s0 q) (hqpc : q.st.st.2 = pcA 4)
    (hg : q.views.Grow t.views) (ht : LInv s0 t) (hpc : t.st.st.2 = pcA 4) (htp : t.prom ≠ [])
    {outs : List (Except String (Outcome isa))} (hs : stepOne Arch.tso t tid mem = some outs) (ho : .ok oc ∈ outs)
    (hrun : ThreadRun Arch.tso tid n (oc.thread, oc.mem) r) (hp : r.1.prom = []) :
    ∃ m, m ≤ a₁ + 1 + n ∧ CertOkN Arch.tso tid s0 mem m := by
  obtain ⟨ts, v, c', ν, hx, hlv, hcm, hcp, hm, hoc⟩ := step_4 ht.sinv hs ho hpc
  -- the run goes on with the `cmpl`
  cases hrun with
  | refl => exact absurd (by rw [← hp, hoc]; exact hcp.symm) htp
  | @step n' _ q2 _ hs2 rest =>
  obtain ⟨outs2, oc2, hs2, ho2, rfl⟩ := hs2
  have hS1 := (step_sinv ht.sinv hs ho).1
  have hpc1 : oc.thread.st.st.2 = pcA 5 := by rw [hoc]; rfl
  rw [hm] at hs2
  obtain ⟨hm2, hoc2⟩ := step_5 hS1 hs2 ho2 hpc1
  -- the replayed read from `q`
  have hiv : (instrViews q { loadDefs := [.r .rcx] }).Dom (instrViews t { loadDefs := [.r .rcx] }) := by
    rw [instrViews_ld, instrViews_ld]
    exact .refl _
  obtain ⟨c₂, hx₂, hd₂⟩ := readSuccs_dom Arch.tso hiv (ctx_dom hqi ht hg) hx
  obtain ⟨t', v', hxe, -, -, -, -⟩ := (mem_readSuccs Arch.tso).mp hx₂
  simp only [Prod.mk.injEq] at hxe
  obtain ⟨rfl, rfl, hc₂⟩ := hxe
  have hat := hqi.sinv.st.at (by decide) (by decide) hqpc
  have hex := exec_ldoX _ hat hqi.sinv.st.dO
  have hr : .ok (goto q.st { q.st.st.1 with regs := q.st.st.1.regs.set64 .rcx (BitVec.setWidth 64
      (BitVec.setWidth 32 v)) } (pcA 5), c₂) ∈
      runTree Arch.tso tid (instrViews q (isa.deps q.st)) (ctx0 tid q mem)
        (.load .plain false ⟨symTk2 "owner", 4⟩ fun v =>
          .done (goto q.st { q.st.st.1 with regs := q.st.st.1.regs.set64 .rcx (BitVec.setWidth 64
            (BitVec.setWidth 32 v)) } (pcA 5))) := by
    rw [deps_4 _ hat]
    simp only [runTree, List.mem_flatMap]
    exact ⟨_, hx₂, run_done_exists Arch.tso tid (instrViews q { loadDefs := [.r .rcx] }) _ _⟩
  obtain ⟨ν₂, hlv₂⟩ : ∃ ν₂, c₂.loadViews = [ν₂] := ⟨_, by rw [hc₂, readNext_loadViews]; rfl⟩
  have hth' : ∃ th : Thread isa, th = ({ q with
      st := goto q.st { q.st.st.1 with regs := q.st.st.1.regs.set64 .rcx (BitVec.setWidth 64
        (BitVec.setWidth 32 v)) } (pcA 5)
      views := c₂.views
      prom := c₂.prom } : Thread isa).setRegView (.r .rcx) ν₂ ν₂ := ⟨_, rfl⟩
  obtain ⟨th, hth⟩ := hth'
  have hrw₂ : c₂.rmwWrote = false := by rw [hc₂, readNext_rmwWrote]
  have hcm₂ : c₂.mem = mem := by rw [hc₂, readNext_mem]
  have hfi : th ∈ finishInstr q (isa.deps q.st) (instrViews q (isa.deps q.st))
      (goto q.st { q.st.st.1 with regs := q.st.st.1.regs.set64 .rcx (BitVec.setWidth 64 (BitVec.setWidth 32 v)) }
        (pcA 5)) c₂ := by
    rw [deps_4 _ hat]
    unfold finishInstr
    simp only [hlv₂, hrw₂, List.foldl_nil, List.foldl_cons, List.length_singleton, Bool.and_false,
      Bool.false_eq_true, ↓reduceIte, List.mem_singleton]
    rw [hth]
    try rfl
  obtain ⟨outs', hs', ho'⟩ := stepOne_of_fi Arch.tso hex hr hfi
  have hν : ν₂ ≤ ν := by
    have := hd₂.loadViews
    rw [hlv, hlv₂] at this
    cases this with
    | cons h1 h2 => exact h1
  -- the replayed `cmpl` from `th`
  have hSth := (step_sinv hqi.sinv hs' ho').1
  have hpcth : th.st.st.2 = pcA 5 := by rw [hth]; rfl
  obtain ⟨outs3, oc3, hs3, ho3, -⟩ := en_done Arch.tso tid (mem := c₂.mem)
    (exec_cmpX _ (hSth.st.at (by decide) (by decide) hpcth))
  obtain ⟨hm3, hoc3⟩ := step_5 hSth hs3 ho3 hpcth
  -- register views at slots 2 and 0 before the `cmpl`
  have hr4 := hqi.rv.le ht.rv hν
  have hw4 := hqi.wv.le ht.wv hν
  have e1 : th.rview = q.rview.setIfInBounds 2 ν₂ := by rw [hth]; simp [Thread.setRegView]; rfl
  have e2 : th.wview = q.wview.setIfInBounds 2 ν₂ := by rw [hth]; simp [Thread.setRegView]; rfl
  have e3 : oc.thread.rview = t.rview.setIfInBounds 2 ν := by rw [hoc]; simp [Thread.setRegView]; rfl
  have e4 : oc.thread.wview = t.wview.setIfInBounds 2 ν := by rw [hoc]; simp [Thread.setRegView]; rfl
  have hV : max (max 0 (max (max 0 (th.rview[2]! : View)) th.rview[0]!)) 0 ≤
      max (max 0 (max (max 0 (oc.thread.rview[2]! : View)) oc.thread.rview[0]!)) 0 := by
    rw [e1, e3]
    exact max_le_max (max_le_max (Nat.le_refl 0) (max_le_max (max_le_max (Nat.le_refl 0) (hr4 2 (by decide)))
      (hr4 0 (by decide)))) (Nat.le_refl 0)
  have hW : max (max 0 (max (max 0 (th.wview[2]! : View)) th.wview[0]!)) 0 ≤
      max (max 0 (max (max 0 (oc.thread.wview[2]! : View)) oc.thread.wview[0]!)) 0 := by
    rw [e2, e4]
    exact max_le_max (max_le_max (Nat.le_refl 0) (max_le_max (max_le_max (Nat.le_refl 0) (hw4 2 (by decide)))
      (hw4 0 (by decide)))) (Nat.le_refl 0)
  have hd : oc3.thread.Dom oc2.thread := by
    rw [hoc3, hoc2]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show goto th.st _ _ = goto oc.thread.st _ _
      rw [hth, hoc]
      exact Core.ld_cmp hqi.core ht.core _ _
    · show ArrLe (th.rview.set! 16 _) (oc.thread.rview.set! 16 _)
      simp only [Array.set!_eq_setIfInBounds]
      rw [e1, e3] at hV ⊢
      exact hqi.rv.arrLe ht.rv hν hV
    · show ArrLe (th.wview.set! 16 _) (oc.thread.wview.set! 16 _)
      simp only [Array.set!_eq_setIfInBounds]
      rw [e2, e4] at hW ⊢
      exact hqi.wv.arrLe ht.wv hν hW
    · show th.views.Dom oc.thread.views
      rw [hth, hoc]; exact hd₂.views
    · show th.prom = oc.thread.prom
      rw [hth, hoc]; exact hd₂.prom
  rw [hm2] at rest
  obtain ⟨r', hr', hdr, -⟩ := rest.toNPn.dom (oc3.thread, mem) hd rfl
  refine ⟨a₁ + 1 + (n' + 1), Nat.le_refl _, r'.1, r'.2, ?_, hdr.prom.trans hp⟩
  have h1 := hq.tail ⟨outs', _, hs', ho', by rw [hcm₂]⟩
  have h2 : ThreadNPn Arch.tso tid (a₁ + 1 + 1) (s0, mem) (oc3.thread, mem) := by
    have := h1.tail (r := (oc3.thread, oc3.mem)) ⟨outs3, oc3, by rw [← hcm₂]; exact hs3, ho3, rfl⟩
    rw [hm3, hcm₂] at this; exact this
  exact (h2.trans hr').mono (by omega)

/-- **A loop run is bounded by `Φ`, or a shorter certification exists**:
induction along the run, carrying the prefix length `a` and the witness of
the repetition. -/
theorem loop_bound : ∀ (n : Nat) (p r : Thread isa × Memory), ThreadRun Arch.tso tid n p r → r.1.prom = [] →
    p.2 = mem → ∀ (a : Nat) (h4 : Bool), ThreadNPn Arch.tso tid a (s0, mem) p → LInv s0 p.1 →
    (h4 = true → W4 tid s0 mem a p.1) →
    (∀ i ∈ [4, 5, 6], p.1.st.st.2 = pcA i → n ≤ Φ i h4) ∨ ∃ m, m < a + n ∧ CertOkN Arch.tso tid s0 mem m := by
  intro n p r h
  induction h with
  | refl p => intro _ _ _ _ _ _ _; exact .inl fun _ _ _ => Nat.zero_le _
  | @step n p q r hs rest ih =>
    intro hp hpm a h4 hpre hI hW4
    obtain ⟨t, mem'⟩ := p
    simp only at hpm hI hW4 hpre
    subst mem'
    -- an empty promise set: the prefix is a certification
    by_cases htp : t.prom = []
    · exact .inr ⟨a, by omega, t, mem, hpre, htp⟩
    obtain ⟨outs, oc, hs, ho, rfl⟩ := hs
    obtain ⟨i, hi, hpc⟩ := hI.pos
    have hpos : ∀ j ∈ [4, 5, 6], t.st.st.2 = pcA j → j = i := fun j hj hj' =>
      addrOf_inj (by simp only [tkPcs, List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega)
        (by simp only [tkPcs, List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega) (hj'.symm.trans hpc)
    obtain ⟨hS', hg, hx', hfw⟩ := step_gen hI.sinv hs ho hI.xclb
    have hW4' : h4 = true → W4 tid s0 mem (a + 1) oc.thread := fun h =>
      let ⟨q, a₁, ha, hq, hqi, hqpc, hgq⟩ := hW4 h; ⟨q, a₁, by omega, hq, hqi, hqpc, hgq.trans hg⟩
    have hpre' : ThreadNPn Arch.tso tid (a + 1) (s0, mem) (oc.thread, oc.mem) := hpre.tail ⟨outs, oc, hs, ho, rfl⟩
    have mk : ∀ (j : Nat), j ∈ [4, 5, 6] → oc.thread.st.st.2 = pcA j → oc.mem = mem →
        oc.thread.prom = t.prom → Core s0.st oc.thread.st → RegS 2 16 s0.rview oc.thread.rview →
        RegS 2 16 s0.wview oc.thread.wview → LInv s0 oc.thread := fun j hj hjpc hm hpr hc hr hw =>
      ⟨⟨j, hj, hjpc⟩, hS', hc, hr, hw, hI.grow.trans hg, (hfw hm hpr).trans hI.fwd, hx', hpr.trans hI.prom⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · -- 4: `movl (owner),%ecx`
      cases h4 with
      | true =>
        obtain ⟨q, a₁, ha, hq, hqi, hqpc, hgq⟩ := hW4 rfl
        obtain ⟨m, hm', hc⟩ := cut_4 hq hqi hqpc hgq hI hpc htp hs ho rest hp
        exact .inr ⟨m, by omega, hc⟩
      | false =>
        obtain ⟨ts, v, c', ν, hx, hlv, hcm, hcp, hm, hoc⟩ := step_4 hI.sinv hs ho hpc
        have hI' : LInv s0 oc.thread := mk 5 (by decide) (by rw [hoc]; rfl) hm (by rw [hoc]; exact hcp)
          (by rw [hoc]; exact hI.core.set4 _ _) (by rw [hoc]; exact hI.rv.set (.inl rfl) ν)
          (by rw [hoc]; exact hI.wv.set (.inl rfl) ν)
        have hW4'' : W4 tid s0 mem (a + 1) oc.thread := ⟨t, a, Nat.lt_succ_self _, hpre, hI, hpc, hg⟩
        rcases ih hp hm (a + 1) true hpre' hI' (fun _ => hW4'') with hb | ⟨m, hm', hc⟩
        · refine .inl fun j hj hj' => ?_
          obtain rfl := hpos j hj hj'
          have := hb 5 (by decide) (by rw [hoc]; rfl)
          simp only [Φ] at this ⊢; omega
        · exact .inr ⟨m, by omega, hc⟩
    · -- 5: `cmpl`
      obtain ⟨hm, hoc⟩ := step_5 hI.sinv hs ho hpc
      have hI' : LInv s0 oc.thread := mk 6 (by decide) (by rw [hoc]; rfl) hm (by rw [hoc]; rfl)
        (by rw [hoc]; exact hI.core.flags _ _) (by rw [hoc]; exact hI.rv.set (.inr rfl) _)
        (by rw [hoc]; exact hI.wv.set (.inr rfl) _)
      rcases ih hp hm (a + 1) h4 hpre' hI' hW4' with hb | ⟨m, hm', hc⟩
      · refine .inl fun j hj hj' => ?_
        obtain rfl := hpos j hj hj'
        have := hb 6 (by decide) (by rw [hoc]; rfl)
        cases h4 <;> simp only [Φ] at this ⊢ <;> omega
      · exact .inr ⟨m, by omega, hc⟩
    · -- 6: `jne`
      obtain ⟨⟨hm, hpr, -⟩, -, hst, -⟩ := q6 hI.sinv.st hs ho hpc
      obtain ⟨hrv, hwv⟩ := step_6 hI.sinv hs ho hpc
      by_cases hz : t.st.st.1.status.zf = true
      · rw [ite_eq_left hz] at hst
        have := tail_bound n _ r rest hS' 7 (by decide) (by rw [hst])
        refine .inl fun j hj hj' => ?_
        obtain rfl := hpos j hj hj'
        cases h4 <;> simp only [Φ, Ψ] at this ⊢ <;> omega
      · rw [ite_eq_right hz] at hst
        have hI' : LInv s0 oc.thread := mk 4 (by decide) (by rw [hst]) hm hpr
          (by rw [hst]; exact hI.core.goto _) (hrv ▸ hI.rv) (hwv ▸ hI.wv)
        rcases ih hp hm (a + 1) h4 hpre' hI' hW4' with hb | ⟨m, hm', hc⟩
        · refine .inl fun j hj hj' => ?_
          obtain rfl := hpos j hj hj'
          have := hb 4 (by decide) (by rw [hst])
          cases h4 <;> simp only [Φ] at this ⊢ <;> omega
        · exact .inr ⟨m, by omega, hc⟩

end Loop

/-! ## The bound -/

/-- `LInv` of a loop state relative to itself. -/
theorem linv_self {t : Thread isa} (hS : SInv t.st) (hx : t.views.xclb = none) {i : Nat}
    (hi : i ∈ [4, 5, 6]) (hpc : t.st.st.2 = pcA i) : LInv t t :=
  ⟨⟨i, hi, hpc⟩, hS, Core.self _, RegS.refl _ _ _, RegS.refl _ _ _, Views.Grow.refl _, rfl, hx, rfl⟩

/-- One step from position `p ∈ {1, 2}` before a bounded continuation. -/
theorem pre_step {s : Thread isa} {mem0 : Memory} {p q B : Nat} (hp : p ∈ tkPcs) (hq : q = nextPc false p)
    (hqz : q = nextPc true p) (hpc : s.st.st.2 = pcA p) (hS0 : SInv s.st) (hx0 : s.views.xclb = none)
    (cont : ∀ (s' : Thread isa) (mem' : Memory), s'.st.st.2 = pcA q → SInv s'.st → s'.views.xclb = none →
      ∀ (k : Nat) (r : Thread isa × Memory), ThreadRun Arch.tso tid k (s', mem') r → r.1.prom = [] → B < k →
      ∃ m, m < k ∧ CertOkN Arch.tso tid s' mem' m)
    (k : Nat) (r : Thread isa × Memory) (hr : ThreadRun Arch.tso tid k (s, mem0) r) (hrp : r.1.prom = [])
    (hk : B + 1 < k) : ∃ m, m < k ∧ CertOkN Arch.tso tid s mem0 m := by
  cases hr with
  | refl => omega
  | @step k' _ q' _ hs rest =>
    obtain ⟨outs, oc, hs, ho, rfl⟩ := hs
    obtain ⟨hS', -, hx', -⟩ := step_gen hS0 hs ho hx0
    have hn := X64Sem2Ticket.pos_step hS0 hp hpc hs ho
    have hn' : oc.thread.st.st.2 = pcA q := by
      cases hz : s.st.st.1.status.zf
      · rw [hz] at hn; rw [hq]; exact hn
      · rw [hz] at hn; rw [hqz]; exact hn
    obtain ⟨m, hm, t', mem', hr', hp'⟩ := cont oc.thread oc.mem hn' hS' hx' k' r rest hrp (by omega)
    exact ⟨m + 1, by omega, t', mem', .step ⟨outs, oc, hs, ho, rfl⟩ hr', hp'⟩

/-- **Every certification of a worker is within `10` instructions.** -/
theorem certOkN_bound {t : Thread isa} {mem : Memory} (hS : SInv t.st) (hx : t.views.xclb = none) {n : Nat}
    (h : CertOkN Arch.tso tid t mem n) : CertOkN Arch.tso tid t mem 10 := by
  refine CertOkN.bound_of_shorter 10 (fun n r hr hp hn => ?_) h
  have loop : ∀ (s0 : Thread isa) (mem0 : Memory) (j : Nat), j ∈ [4, 5, 6] → s0.st.st.2 = pcA j →
      SInv s0.st → s0.views.xclb = none → ∀ (k : Nat) (r : Thread isa × Memory),
      ThreadRun Arch.tso tid k (s0, mem0) r → r.1.prom = [] → Φ j false < k →
      ∃ m, m < k ∧ CertOkN Arch.tso tid s0 mem0 m := by
    intro s0 mem0 j hj hjpc hS0 hx0 k r hr hp hk
    rcases loop_bound k (s0, mem0) r hr hp rfl 0 false (.refl _ _) (linv_self hS0 hx0 hj hjpc)
        (fun h => Bool.noConfusion h) with hb | ⟨m, hm, hc⟩
    · exact absurd (hb j hj hjpc) (Nat.not_le_of_lt hk)
    · exact ⟨m, by omega, hc⟩
  -- the steps before the loop: `lock xaddl` (2), then `movl $1,%eax` (1)
  have pre2 := fun s mem0 hpc hS0 hx0 => pre_step (tid := tid) (s := s) (mem0 := mem0) (p := 2) (q := 4)
    (B := 8) (by decide) rfl rfl hpc hS0 hx0 (fun s' mem' hpc' hS' hx' => loop s' mem' 4 (by decide) hpc' hS' hx')
  have pre1 := fun s mem0 hpc hS0 hx0 => pre_step (tid := tid) (s := s) (mem0 := mem0) (p := 1) (q := 2)
    (B := 9) (by decide) rfl rfl hpc hS0 hx0 (fun s' mem' hpc' hS' hx' k r hr hrp hk =>
      pre2 s' mem' hpc' hS' hx' k r hr hrp (by omega))
  have hlt : ∀ j, Φ j false < n := fun j => Nat.lt_of_le_of_lt (Φ_le j false) hn
  obtain ⟨hSt, i, hi, hpc⟩ := id hS
  simp only [tkPcs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pre1 t mem hpc hS hx n r hr hp (by omega)
  · exact pre2 t mem hpc hS hx n r hr hp (by omega)
  · exact loop t mem 4 (by decide) hpc hS hx n r hr hp (hlt 4)
  · exact loop t mem 5 (by decide) hpc hS hx n r hr hp (hlt 5)
  · exact loop t mem 6 (by decide) hpc hS hx n r hr hp (hlt 6)
  all_goals exact absurd (tail_bound n _ r hr hS _ (by decide) hpc) (by simp only [Ψ]; omega)

/-! ## Reachable configurations -/

/-- **Bounded certification from every start configuration**: `F = 10`. -/
theorem ticket2_x64_certBounded {N : Nat} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : Ticket2X64.Tk2StartX N states initMem) :
    CertBoundedFrom Arch.tso (Config.init states initMem) 10 := by
  intro fuel cfg hr tid t n ht hc
  have hinv := NoStuck.reachableSem_inv (fun cfg => InvP fuel N cfg ∧ XclbNone cfg)
    (fun tid cfg cfg' ⟨hI, hX⟩ hst => by
      obtain ⟨t, ht⟩ : ∃ t, cfg.threads[tid]? = some t := by
        rcases hst with ⟨t, -, -, ht, -⟩ | ⟨t, -, ht, -⟩ <;> exact ⟨t, ht⟩
      exact ⟨(inv_step hI ht hst).1, xclbNone_step hX (fun u _ _ hu hs ho hx =>
        (step_gen (hI.thr _ u hu).sinv hs ho hx).2.2.1) hst⟩) hr ⟨inv_init hs, xclbNone_init _ _⟩
  exact certOkN_bound (hinv.1.thr tid t ht).sinv (hinv.2 tid t ht) hc

/-! ## The fuel-free theorems -/

/-- `X64Sem2.Ticket2X64LiveSem` on the fuel-free semantic machine. -/
def Ticket2X64LiveSemU : Prop :=
  ∀ N states initMem, Ticket2X64.Tk2StartX N states initMem →
    LiveFromSemU Arch.tso (Config.init states initMem)
      (fun cfg => WeakFairSemU Arch.tso cfg ∧ MemFair Arch.tso cfg) Ticket2X64.Tk2WaitingX Ticket2X64.Tk2DoneX

/-- **x64 ticketlock2 liveness with promises, fuel-free**:
`ticket2_x64_live_sem` at fuel `10` through `liveTransfer`. On every trace of
the fuel-free semantic machine from a start configuration, under fuel-free
weak fairness and memory fairness, every waiting thread is eventually done. -/
theorem ticket2_x64_live_semU : Ticket2X64LiveSemU := fun N states initMem hs =>
  liveTransfer (ticket2_x64_certBounded hs) (X64Sem2Ticket.ticket2_x64_live_sem 10 N states initMem hs)

end Kraken.Promising.Live.CertBoundedTicket2X64

/-! ## A concrete instance (outside the section's layout variables, so that
the statement has no layout binder) -/

namespace Kraken.Promising.Live.CertBoundedTicket2X64

open Kraken.Promising.X64.EnvG.TicketX2.Concrete in
/-- `ticket2_x64_live_semU` at the `.kl` runner's layout `tk2LayoutV`: no
hypothesis and no binder left. -/
theorem ticket2_x64_live_semU_concrete : @Ticket2X64LiveSemU tk2LayoutV :=
  @ticket2_x64_live_semU tk2LayoutV tk2ValidV

end Kraken.Promising.Live.CertBoundedTicket2X64
