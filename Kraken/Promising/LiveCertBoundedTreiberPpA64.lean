/-
**Bounded certification for the AArch64
`treiber_pp.kl` image** (`treiberImageA`, valid layout, declarations agreeing
on `top`, the node's data word and its link word): `CertBoundedFrom
Arch.armv8 c0 51` for the start configurations of `treiber_pp_live_gen`
(`LiveTreiberPpA64.lean`). Everything here is on the
*semantic* machine (`StepSem`/`ReachableSem`, `Arch.armv8`).

## The bound `F = 51`

`CertOkN.bound_of_shorter`: a certifying solo run longer than `51`
instructions is not the shortest one. Along a solo run the potential `R`
drops at every step, except where the run can be cut.

- **Headroom** (`head_of_certOkN`, the `LiveCertBoundedTreiber2P` recipe):
  along a solo run, `S + promAt top` (successful `CASAL`s plus outstanding
  promises to `top`) never drops, and a certifying run ends with no promise
  and `S ≤ 1`. So every reachable thread has `S + promAt top ≤ 1` (`InvH`,
  proved along `ReachableSem` at every fuel, beside the existing `Inv`). With
  the existing count field there are at most `2` writes to `top`, and along a
  solo run at most `3 = N` (`SoloP`).
- **The rank** (`rk`, the `treiber2` rank of `LiveTermTreiber2.lean` on this
  program's positions): with `V = 10 * (3 - cnt)` (`cnt`/`cur`: writes to
  `top` at or below the coherence view and the current value there), a
  retry loop costs `V` plus a position offset, plus `fl = 10` while `X2` is
  not `cur`. A failed `CASAL` with `X2 = cur` read a value other than `cur`,
  so `cnt` grew (`window_rank`). The link store of the push retry writes
  `n + 8 ≠ top`, so it leaves `cnt` and `cur` alone. The branch cells read
  the success count `S` (`sOf`).
- **The empty spin** (`LDAR X2,[X0]; CBZ X2,popper`) is read-only and is
  cut. The witness is a visit of `CBZ` (position `14`) with `X2 = 0`,
  reached by an `LDAR` of this run, so `X2`'s register view (the read's
  post-view `ν`) is at most `vrNew` (`LDAR` is an acquire load). The next
  `LDAR` reading `0` from the following loop head reaches the same machine
  state. Its post-view is at least its `readPre`, which is at least `vrNew`,
  which has grown from the witness. So the witness *dominates* the later
  state (`Thread.Dom`), and the loop between them is cut
  (`ThreadNPn.dom`, `cut_13`). Nothing is replayed.

`F = 21 + 10 * 3` depends on the program only: not on the fuel or the layout.

## Headlines

`treiber_pp_certBounded` (no declarations) and
`treiber_pp_certBounded_runner` (the runner's declarations); with
`CertBounded.liveTransfer`, the existing `treiber_pp_live_sem` /
`treiber_pp_live_runner` at fuel `51` become the fuel-free
`treiber_pp_live_semU` / `treiber_pp_live_runner_semU` (and `_concrete`),
under `WeakFairSemU ∧ MemFair`, with no extra hypothesis.
-/
import Kraken.Promising.LiveTreiberPpA64Runner
import Kraken.Promising.LiveCertBoundedTreiber2P
import Kraken.Promising.LiveCertBoundedSpinCas

namespace Kraken.Promising.Live.CertBoundedTreiberPpA64

set_option linter.unusedSectionVars false

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live Kraken.Promising.Live.Sem
open Kraken.Promising.Live.Term Kraken.Promising.Live.CertBounded Kraken.Promising.Live.CertCut
open Kraken.Promising.Live.TreiberPpA64 Kraken.Promising.Live.TicketStep
open Kraken.Promising.SLR.EnvG.Treiber (treiberImageA treiberImageA_wf)
open Kraken.Promising.SLR.A64Trees (goto)
open Kraken.Promising.Live.TermTreiber2 (fl)
open Kraken.Promising.Live.TermTreiber2P (rank_body fl_le)

/-! ## The rank -/

/-- **The rank at position `p`** (registers `s`, witness flag `h`, `cnt`
writes to `top` at or below the coherence view, current value `cur`), with
`V = 10 * (3 - cnt)`. -/
def rk (p : Nat) (s : MachineData) (h : Bool) (cnt : Nat) (cur : Val) : Nat :=
  match p with
  | 1 => 43
  | 3 => 12 + 10 * (3 - cnt)
  | 4 => 11 + 10 * (3 - cnt) + fl s cur
  | 5 => 10 + 10 * (3 - cnt) + fl s cur
  | 6 => 9 + 10 * (3 - cnt) + fl s cur
  | 7 => if sOf 7 s = 1 then 3 else 15 + 10 * (3 - cnt)
  | 8 => if sOf 8 s = 1 then 2 else 14 + 10 * (3 - cnt)
  | 9 => 1
  | 13 => if h then 12 + 10 * (3 - cnt) else 14 + 10 * (3 - cnt)
  | 14 => if s.regs.X2.toBitVec = 0#64 then (if h then 13 + 10 * (3 - cnt) else 15 + 10 * (3 - cnt))
      else 11 + 10 * (3 - cnt) + fl s cur
  | 15 => 10 + 10 * (3 - cnt) + fl s cur
  | 16 => 9 + 10 * (3 - cnt) + fl s cur
  | 17 => 8 + 10 * (3 - cnt) + fl s cur
  | 18 => if sOf 18 s = 1 then 5 else 16 + 10 * (3 - cnt)
  | 19 => if sOf 19 s = 1 then 4 else 15 + 10 * (3 - cnt)
  | 20 => 3
  | 21 => 2
  | 22 => 1
  | _ => 0

theorem rk_le (p : Nat) (s : MachineData) (h : Bool) (cnt : Nat) (cur : Val) : rk p s h cnt cur ≤ 51 := by
  have := fl_le s cur
  unfold rk; split <;> (try split) <;> (try split) <;> omega

/-- The witness flag after a step from position `p` (registers `s` before,
`s'` after): set on reaching `CBZ` with `X2 = 0`, kept from `CBZ` back to
the loop head. -/
def nextH (p : Nat) (s s' : MachineData) (h : Bool) : Bool :=
  if p = 13 then decide (s'.regs.X2.toBitVec = 0#64) else if p = 14 then h && decide (s.regs.X2.toBitVec = 0#64)
  else false

/-- `cnt` and `cur` of a thread. -/
abbrev cntT (t : BitVec 64) (u : Thread isa) (mem : Memory) : Nat := mem.cntBelow (topL t) (u.views.getCoh (topL t))
abbrev curT (t : BitVec 64) (u : Thread isa) (mem : Memory) : Val := mem.curBelow (topL t) (u.views.getCoh (topL t))

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout treiberImageA)]

set_option hygiene false in
local notation "pcT" => (layout treiberImageA).addrOf

/-- A thread's rank. -/
def R (h : Bool) (t : BitVec 64) (u : Thread isa) (mem : Memory) : Nat :=
  rk (pos u) u.st.st.1 h (cntT t u mem) (curT t u mem)

/-! ## The cells of the empty spin, refined -/

/-- Read the dependencies of the cell at position `i`. -/
local macro "a64deps" h:ident i:num : tactic => `(tactic| (
  have hc := Kraken.Executable.codeAt_addrOf (p := treiberImageA) (i := $i) (d := treiberImageA[$i])
    (by decide) (by decide)
  rw [← ($h).pc] at hc
  generalize hd : treiberImageA[$i] = d at hc
  simp only [treiberImageA, List.getElem_cons_succ, List.getElem_cons_zero] at hd
  subst hd
  have hdir := CertBoundedSpinCas.directive_of_codeAt (by rw [($h).exe]; exact hc)
  show AArch64.deps _ = _
  unfold AArch64.deps
  rw [hdir]
  rfl))

theorem deps_13 (st : State) (h : AtD st 13) : isa.deps st = { addrRegs := [.x 0], loadDefs := [.x 2] } := by
  a64deps h 13
theorem deps_14 (st : State) (h : AtD st 14) : isa.deps st = { condRegs := [.x 2], isBranch := true } := by
  a64deps h 14

set_option maxRecDepth 8192 in
/-- `ldar x2, [x0]` at position `13`, with its load kind (acquire). -/
theorem exec_ldar13 (st : State) (h : AtD st 13) {t : BitVec 64} (hag : st.decls.AgreesAt t 8)
    (hx0 : st.st.1.regs.X0.toBitVec = t) (hdm : Mem.loadInt st.st.1.dmem t 8 = none) :
    isa.exec st = some (.load .acq false ⟨t, 8⟩
      fun v => .done (goto st { st.st.1 with regs := st.st.1.regs.setXReg .X2 (BitVec.setWidth 64 v) } (pcT 14))) := by
  have hnext : pcT 14 = st.st.2 + .ofNat (Kraken.Layout.size Directive 13) := by
    rw [h.pc]; exact SLR.A64Trees.addrOf_step (by decide)
  rw [hnext]
  have hc := Kraken.Executable.codeAt_addrOf (p := treiberImageA) (i := 13) (d := (treiberImageA)[13]) (by decide)
    (by decide)
  rw [← h.pc] at hc
  generalize hd : (treiberImageA)[13] = d at hc
  simp only [treiberImageA, List.getElem_cons_succ, List.getElem_cons_zero] at hd
  subst hd
  rw [exec_eq_of_codeAtD h.exe h.ne hc]
  simp only [Directive.interp, Instr.interp, Operation.interp]
  simp [toEv, RegOrSp.interpBase, MachineData.loadK, EvTree.map, Reg64s.getRegOrSp, Reg64s.getRegOrSp64,
    RegOrSp.base, MachineData.setRegOrZr, Reg64s.getXReg, goto, EvTree.access_empty, hx0, hdm,
    EvTree.access_of_agreesAt hag]

section Spin

variable {ds : Decls} {t n : BitVec 64} {u : Thread isa} {tid : Nat} {mem : Memory}
  {outs : List (Except String (Outcome isa))} {oc : Outcome isa}
  {r : Nat} (hS : Static ds t n r u.st) (hs : stepOne Arch.armv8 u tid mem = some outs) (ho : .ok oc ∈ outs)
include hS hs ho

/-- **The `LDAR` of the spin** (position `13`): `X2 := v` with register view
the read's post-view `ν`, which lies between `vrNew` before and after. -/
theorem step_13 (hi : 13 ∈ pcsR r) (hT : ds.AgreesAt t 8) (hpc : u.st.st.2 = pcT 13) :
    ∃ (v : Val) (c' : Ctx) (ν : View), oc.mem = mem ∧ c'.prom = u.prom ∧ c'.views.xclb = u.views.xclb ∧
      u.views.vrNew ≤ ν ∧ ν ≤ c'.views.vrNew ∧ oc.thread =
      { u with
        st := goto u.st { u.st.st.1 with regs := u.st.st.1.regs.setXReg .X2 (BitVec.setWidth 64 v) } (pcT 14)
        views := c'.views
        prom := c'.prom }.setRegView (.x 2) ν ν := by
  have hat : AtD u.st 13 := hS.at hi (by unfold endP; split <;> decide) hpc
  obtain ⟨tree, st, c', hex, hr, hfi, hm⟩ := stepOne_fi Arch.armv8 hs ho
  rw [exec_ldar13 _ hat (by rw [hS.decls]; exact hT) hS.x0 hS.dt] at hex
  obtain rfl := Option.some.inj hex
  rw [deps_13 _ hat] at hr hfi
  obtain ⟨ts, v, hx, rfl⟩ := run_load_ctx Arch.armv8 tid _ hr
  obtain ⟨t', v', hxe, -, -, -, -⟩ := (mem_readSuccs Arch.armv8).mp hx
  simp only [Prod.mk.injEq] at hxe
  obtain ⟨rfl, rfl, rfl⟩ := hxe
  have hlv := readNext_loadViews Arch.armv8 (instrViews u { addrRegs := [.x 0], loadDefs := [.x 2] })
    (ctx0 tid u mem) .acq false (topL t) false ts v
  have hrw := readNext_rmwWrote Arch.armv8 (instrViews u { addrRegs := [.x 0], loadDefs := [.x 2] })
    (ctx0 tid u mem) .acq false (topL t) false ts v
  refine ⟨v, _, _, hm.trans (readNext_mem _ _ _ _ _ _ _ _ _), readNext_prom _ _ _ _ _ _ _ _ _, rfl, ?_, ?_,
    finishInstr_load1 rfl rfl rfl hrw rfl hlv hfi⟩
  · show _ ≤ max (readPre Arch.armv8 _ _ .acq) _
    unfold readPre
    exact Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) (Nat.le_max_left _ _)
  · exact Nat.le_max_right _ _

/-- **The `CBZ` of the spin** (position `14`): no write, registers and their
views unchanged, views grown, the forwarding table and the pending-exclusive
slot unchanged. -/
theorem step_14 (hi : 14 ∈ pcsR r) (hpc : u.st.st.2 = pcT 14) :
    oc.mem = mem ∧ oc.thread.prom = u.prom ∧
      oc.thread.st = goto u.st u.st.st.1 (if u.st.st.1.regs.X2.toBitVec = 0#64 then pcT 13 else pcT 15) ∧
      oc.thread.rview = u.rview ∧ oc.thread.wview = u.wview ∧ oc.thread.views.xclb = u.views.xclb ∧
      u.views.Grow oc.thread.views ∧ oc.thread.views.fwdb = u.views.fwdb := by
  have hat : AtD u.st 14 := hS.at hi (by unfold endP; split <;> decide) hpc
  obtain ⟨hm, hst, hp, -⟩ := TicketStep.spec_done _ _ (exec_cbz14 _ hat) hs ho
  obtain ⟨tree, st, c', hex, hr, hfi, -⟩ := stepOne_fi Arch.armv8 hs ho
  rw [exec_cbz14 _ hat] at hex
  obtain rfl := Option.some.inj hex
  obtain ⟨-, rfl⟩ := run_done Arch.armv8 tid _ hr
  rw [deps_14 _ hat] at hfi
  obtain ⟨hrv, hwv⟩ := finishInstr_regs_nil rfl rfl rfl hfi
  obtain ⟨hg, -, hnw⟩ := stepOne_grow Arch.armv8 hs ho
  refine ⟨hm, hp, hst, hrv, hwv, ?_, hg, ((hnw (by rw [hm])).2 (by rw [hp])).1⟩
  rcases finishInstr_views hfi with e | e <;> rw [e] <;> rfl

end Spin

/-! ## Headroom, and the fuel-free invariant -/

/-- A semantic step extends memory. -/
theorem stepSem_prefix {fuel tid : Nat} {c c' : Config isa} (h : StepSem Arch.armv8 fuel tid c c') :
    c.mem.Prefix c'.mem := by
  rcases h with ⟨u, outs, o, -, hs, ho, -, rfl⟩ | ⟨u, w, -, -, -, rfl⟩
  · exact (stepOne_dord _ hs ho).2.2.1
  · exact Memory.Prefix.append _ _

section Head

variable {ds : Decls} {t n : BitVec 64} (hT : ds.AgreesAt t 8) (hD : ds.AgreesAt n 4)
  (hN : ds.AgreesAt (n + 8#64) 8) (htn : t ≠ n + 8#64)
include hT hD hN htn

/-- **What one step of a thread alone does** to the writes to `top`, its
successful `CASAL`s `S` and its promises to `top`. -/
theorem solo_step {r tid : Nat} {u : Thread isa} {mem : Memory} {outs : List (Except String (Outcome isa))}
    {o : Outcome isa} (hS : Static ds t n r u.st) (hP : PcOK r u.st) (hpl : ∀ ts ∈ u.prom, ts ≤ mem.last)
    (hs : stepOne Arch.armv8 u tid mem = some outs) (ho : .ok o ∈ outs) :
    StepOK ds t n r u mem o ∧ (∀ ts ∈ o.thread.prom, ts ≤ o.mem.last) ∧
      o.mem.cntBelow (topL t) o.mem.last + (S u + mem.promAt (topL t) u.prom) ≤
        mem.cntBelow (topL t) mem.last + (S o.thread + o.mem.promAt (topL t) o.thread.prom) ∧
      mem.cntBelow (topL t) mem.last ≤ o.mem.cntBelow (topL t) o.mem.last ∧
      o.mem.cntBelow (topL t) o.mem.last + S u ≤ mem.cntBelow (topL t) mem.last + S o.thread := by
  have q := thread_step hT hD hN htn hS hs ho hP
  refine ⟨q, ?_⟩
  rcases q.eff with ⟨hm, hp, hle⟩ | ⟨w, hw, hle, -⟩
  · rw [hm, hp]; exact ⟨hpl, by omega, Nat.le_refl _, by omega⟩
  · obtain ⟨e, hpl'⟩ := count_weff (l := topL t) hpl hw
    obtain ⟨c1, c2⟩ := CertBoundedTreiber2P.cnt_weff (topL t) hw
    exact ⟨hpl', by omega, c1, by omega⟩

/-- **Headroom along a certifying run**: `S + promAt top` never drops along a
run of a thread alone, and is at most `1` where the promise set is empty. -/
theorem head_of_threadNPn {r tid : Nat} :
    ∀ {k : Nat} {p q : Thread isa × Memory}, ThreadNPn Arch.armv8 tid k p q → q.1.prom = [] →
      Static ds t n r p.1.st → PcOK r p.1.st → (∀ ts ∈ p.1.prom, ts ≤ p.2.last) →
      S p.1 + p.2.promAt (topL t) p.1.prom ≤ 1 := by
  intro k p q h
  induction h with
  | refl k p =>
    intro hq _ _ _
    have : S p.1 ≤ 1 := sOf_le _ _
    rw [hq]; simp only [Memory.promAt, List.countP_nil]; omega
  | step hs _ ih =>
    intro hq hS hP hpl
    obtain ⟨outs, o, hs, ho, rfl⟩ := hs
    obtain ⟨r, hpl', h1, h2, -⟩ := solo_step hT hD hN htn hS hP hpl hs ho
    have := ih hq r.st r.pc hpl'
    dsimp only at this
    omega

/-- **A certifiable thread has `S + promAt top ≤ 1`** (at any fuel). -/
theorem head_of_certOkN {r tid k : Nat} {u : Thread isa} {mem : Memory} (hc : CertOkN Arch.armv8 tid u mem k)
    (hS : Static ds t n r u.st) (hP : PcOK r u.st) (hpl : ∀ ts ∈ u.prom, ts ≤ mem.last) :
    S u + mem.promAt (topL t) u.prom ≤ 1 := by
  obtain ⟨u', mem', h, hp⟩ := hc
  exact head_of_threadNPn (r := r) (tid := tid) (p := (u, mem)) (q := (u', mem')) hT hD hN htn h hp hS hP hpl

omit hT hD hN htn in
/-- **The fuel-free per-thread facts** beside the existing `Inv`: forwarding
below coherence, and the headroom. -/
def InvH (t : BitVec 64) (c : Config isa) : Prop :=
  ∀ (i : Nat) (u : Thread isa), c.threads[i]? = some u →
    Witness.FwdLeCoh u.views ∧ S u + c.mem.promAt (topL t) u.prom ≤ 1

omit hT hD hN htn in
theorem InvH.init {states : List isa.State} {initMem : List (Loc × Val)} :
    InvH t (Config.init states initMem) := by
  intro i u hu
  simp only [Config.init, List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at hu
  obtain ⟨s, -, rfl⟩ := hu
  have : S (Thread.init s : Thread isa) ≤ 1 := sOf_le _ _
  have hp : (Thread.init s : Thread isa).prom = [] := by simp [Thread.init]
  exact ⟨Witness.fwdLeCoh_of_nil rfl, by rw [hp]; simp only [Memory.promAt, List.countP_nil]; omega⟩

/-- **A semantic step at any fuel keeps `InvH`**: the stepping thread's
headroom comes from the certification the step carries (instruction and
promise steps alike); the other threads' promises keep their messages. -/
theorem InvH.step {fuel tid : Nat} {c c' : Config isa} (hI : Inv ds t n fuel c) (hH : InvH t c)
    (hst : StepSem Arch.armv8 fuel tid c c') : InvH t c' := by
  have hI' : Inv ds t n fuel c' := by
    obtain ⟨u, hu⟩ := TreiberPp.stepSem_get hst
    exact hI.step hT hD hN htn hu hst
  intro i u' hu'
  by_cases e : i = tid
  · subst e
    obtain ⟨t', ht', hc⟩ := TreiberPp.certOkN_of_stepSem hst
    have e2 : t' = u' := Option.some.inj (ht'.symm.trans hu')
    subst e2
    have hTI := hI'.thr i t' ht'
    refine ⟨?_, head_of_certOkN hT hD hN htn hc hTI.st hTI.pc hTI.promLe⟩
    rcases hst with ⟨u, outs, o, hu, hs, ho, -, rfl⟩ | ⟨u, w, hu, -, -, rfl⟩
    · rw [withThread_get_self hu] at ht'; cases ht'; exact Witness.stepOne_fwdLeCoh hs ho (hH i u hu).1
    · rw [withThread_get_self hu] at ht'; cases ht'; exact (hH i u hu).1
  · rw [TreiberPp.get_of_stepSem_ne hst e] at hu'
    refine ⟨(hH i u' hu').1, ?_⟩
    rw [promAt_prefix (stepSem_prefix hst) (hI.thr i u' hu').promLe]; exact (hH i u' hu').2

end Head

/-! ## The rank drops at every step but the cut -/

section Rank

variable {ds : Decls} {t n : BitVec 64} (hT : ds.AgreesAt t 8) (hD : ds.AgreesAt n 4)
  (hN : ds.AgreesAt (n + 8#64) 8) (htn : t ≠ n + 8#64)
include hT hD hN htn

/-- **One step lowers the rank**, given forwarding below coherence, the
coherence view within memory and at most `3` writes to `top` after the step;
except an `LDAR` from a flagged loop head reading `0` (the cut). -/
theorem rank_step {r tid : Nat} {u : Thread isa} {mem : Memory} {outs : List (Except String (Outcome isa))}
    {o : Outcome isa} (hS : Static ds t n r u.st) (hP : PcOK r u.st)
    (hs : stepOne Arch.armv8 u tid mem = some outs) (ho : .ok o ∈ outs) (hf : Witness.FwdLeCoh u.views)
    (hb : u.views.getCoh (topL t) ≤ mem.last) (hN3 : cntT t o.thread o.mem ≤ 3) {h : Bool}
    (hcut : pos u = 13 → h = true → o.thread.st.st.1.regs.X2.toBitVec ≠ 0#64) :
    R (nextH (pos u) u.st.st.1 o.thread.st.st.1 h) t o.thread o.mem < R h t u mem := by
  have q := thread_step hT hD hN htn hS hs ho hP
  obtain ⟨i, hi, hpc, hI⟩ := hP
  have hpu : pos u = i := by rw [pos, hpc, posOf_pcT (mem_tPcs hi)]
  have hpo : pos o.thread = nextP i u.st.st.1 := by rw [q.nx, hpu]
  have hSle : sOf i u.st.st.1 ≤ sOf (nextP i u.st.st.1) o.thread.st.st.1 := by
    have : S u ≤ S o.thread := by rcases q.eff with ⟨-, -, e⟩ | ⟨w, -, e, -⟩ <;> omega
    simpa only [S, hpu, hpo] using this
  have hc := step_cnt (l := topL t) (stepOne_dord _ hs ho).2.2.1 hb ((stepOne_dord _ hs ho).2.1 _)
  have hx2 := q.x2
  have hne : ∀ j, j ≠ 11 → j ≠ 24 → j ≠ endP r := fun j h1 h2 => by unfold endP; split <;> assumption
  have hdT : u.st.decls.AgreesAt t 8 := by rw [hS.decls]; exact hT
  rw [hpu] at hcut hx2
  unfold R cntT curT at *
  rw [hpu, hpo]
  have hil := mem_tPcs hi
  simp only [tPcs, List.mem_cons, List.not_mem_nil, or_false] at hil
  rcases hil with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · rw [show nextP 1 u.st.st.1 = 3 from rfl]; simp only [rk]; omega
  · -- 3: `LDAR`
    obtain ⟨k, hex⟩ := exec_ldar 3 (.inl rfl) _ (hS.at hi (hne 3 (by decide) (by decide)) hpc) hdT hS.x0 hS.dt
    obtain ⟨ts, v, hst, hm, -, hr, h1, h2⟩ := load_window _ _ hf hex hs ho
    have hw := window_rank (Memory.Prefix.refl mem) hb hr h1 h2
    have hx : o.thread.st.st.1.regs.X2.toBitVec = BitVec.setWidth 64 v := by rw [hst]; simp
    rw [show nextP 3 u.st.st.1 = 4 from rfl]
    rw [hm] at hc hN3 ⊢
    have hfl : fl o.thread.st.st.1 (curT t o.thread mem) =
        if BitVec.setWidth 64 v = BitVec.setWidth 64 (curT t o.thread mem) then 0 else 10 := by
      simp only [fl, hx]
    simp only [rk, hfl]
    by_cases he : BitVec.setWidth 64 v = BitVec.setWidth 64 (curT t o.thread mem)
    · simp only [he, ↓reduceIte, topL] at hc hN3 ⊢; omega
    · have := hw.2 fun e => he (by rw [e])
      simp only [he, ↓reduceIte, topL] at hc hN3 this ⊢
      omega
  · rw [show nextP 4 u.st.st.1 = 5 from rfl]; simp only [rk]
    exact rank_body (hx2 (by decide) (by decide)) hN3 hc (by omega)
  · rw [show nextP 5 u.st.st.1 = 6 from rfl]; simp only [rk]
    exact rank_body (hx2 (by decide) (by decide)) hN3 hc (by omega)
  · -- 6: `CASAL`
    obtain ⟨k, hex⟩ := exec_casal 6 (.inl rfl) _ (hS.at hi (hne 6 (by decide) (by decide)) hpc) hdT hS.x0 hS.dt
    simp only [↓reduceIte] at hex
    obtain ⟨ts, v, hst, hr, h1, h2⟩ := rmw_window _ _ rfl hf hex hs ho
    have hw := window_rank (stepOne_dord _ hs ho).2.2.1 hb hr h1 h2
    have hx3 : o.thread.st.st.1.regs.X3.toBitVec = BitVec.setWidth 64 v := by rw [hst]; simp
    have hx : o.thread.st.st.1.regs.X2 = u.st.st.1.regs.X2 := hx2 (by decide) (by decide)
    have e7 : sOf 7 o.thread.st.st.1 = if BitVec.setWidth 64 v = u.st.st.1.regs.X2.toBitVec then 1 else 0 := by
      simp [sOf, hx3, hx]
    rw [show nextP 6 u.st.st.1 = 7 from rfl]
    by_cases hv : BitVec.setWidth 64 v = u.st.st.1.regs.X2.toBitVec
    · rw [ite_eq_left hv] at e7
      simp only [rk, e7, ↓reduceIte]; have := fl_le u.st.st.1 (curT t u mem); omega
    · rw [ite_eq_right hv] at e7
      simp only [rk, e7, Nat.zero_ne_one, ↓reduceIte]
      by_cases he : u.st.st.1.regs.X2.toBitVec = BitVec.setWidth 64 (curT t u mem)
      · have := hw.1 fun e => hv (by rw [e]; exact he.symm)
        rw [show fl u.st.st.1 (curT t u mem) = 0 from ite_eq_left he]
        simp only [topL] at hc hN3 this ⊢
        omega
      · rw [show fl u.st.st.1 (curT t u mem) = 10 from ite_eq_right he]
        simp only [topL] at hc hN3 ⊢
        omega
  · rw [show nextP 7 u.st.st.1 = 8 from rfl] at hSle ⊢
    simp only [rk]
    have := sOf_le 8 o.thread.st.st.1
    split <;> split <;> omega
  · by_cases hz : u.st.st.1.status.z = true <;> simp [nextP, rk, sOf, hz] <;> omega
  · rw [show nextP 9 u.st.st.1 = 11 from rfl]; simp [rk]
  · rw [stepOne_end' hS (by rw [hpc, (by unfold endP; split <;> simp_all [pcsR] : endP r = 11)])] at hs; cases hs
  · -- 13: `LDAR`
    obtain ⟨k, hex⟩ := exec_ldar 13 (.inr rfl) _ (hS.at hi (hne 13 (by decide) (by decide)) hpc) hdT hS.x0 hS.dt
    obtain ⟨ts, v, hst, hm, -, hr, h1, h2⟩ := load_window _ _ hf hex hs ho
    have hw := window_rank (Memory.Prefix.refl mem) hb hr h1 h2
    have hx : o.thread.st.st.1.regs.X2.toBitVec = BitVec.setWidth 64 v := by rw [hst]; simp
    rw [hx] at hcut
    rw [show nextP 13 u.st.st.1 = 14 from rfl,
      show nextH 13 u.st.st.1 o.thread.st.st.1 h = decide (o.thread.st.st.1.regs.X2.toBitVec = 0#64) from rfl]
    rw [hm] at hc hN3 ⊢
    have hfl : fl o.thread.st.st.1 (curT t o.thread mem) =
        if BitVec.setWidth 64 v = BitVec.setWidth 64 (curT t o.thread mem) then 0 else 10 := by
      simp only [fl, hx]
    simp only [rk, hx, hfl]
    by_cases hz : BitVec.setWidth 64 v = 0#64
    · cases h
      · simp only [hz, decide_true, ↓reduceIte, Bool.false_eq_true]
        simp only [topL] at hc hN3 ⊢; omega
      · exact absurd hz (hcut rfl rfl)
    · rw [ite_eq_right hz]
      by_cases he : BitVec.setWidth 64 v = BitVec.setWidth 64 (curT t o.thread mem)
      · rw [ite_eq_left he]
        simp only [topL] at hc hN3 ⊢
        cases h <;> simp only [↓reduceIte, Bool.false_eq_true] <;> omega
      · have := hw.2 fun e => he (by rw [e])
        rw [ite_eq_right he]
        simp only [topL] at hc hN3 this ⊢
        cases h <;> simp only [↓reduceIte, Bool.false_eq_true] <;> omega
  · -- 14: `CBZ`
    by_cases hz : u.st.st.1.regs.X2.toBitVec = 0#64
    · have e : nextP 14 u.st.st.1 = 13 := by simp [nextP, hz]
      rw [e, show nextH 14 u.st.st.1 o.thread.st.st.1 h = (h && decide (u.st.st.1.regs.X2.toBitVec = 0#64)) from rfl]
      simp only [rk, hz, ↓reduceIte, decide_true, Bool.and_true]
      split <;> omega
    · have e : nextP 14 u.st.st.1 = 15 := by simp [nextP, hz]
      rw [e]
      simp only [rk, hz, ↓reduceIte]
      exact rank_body (hx2 (by decide) (by decide)) hN3 hc (by omega)
  · rw [show nextP 15 u.st.st.1 = 16 from rfl]; simp only [rk]
    exact rank_body (hx2 (by decide) (by decide)) hN3 hc (by omega)
  · rw [show nextP 16 u.st.st.1 = 17 from rfl]; simp only [rk]
    exact rank_body (hx2 (by decide) (by decide)) hN3 hc (by omega)
  · -- 17: `CASAL`
    obtain ⟨k, hex⟩ := exec_casal 17 (.inr rfl) _ (hS.at hi (hne 17 (by decide) (by decide)) hpc) hdT hS.x0 hS.dt
    simp only [show (17 = 6) = False by decide, ↓reduceIte] at hex
    obtain ⟨ts, v, hst, hr, h1, h2⟩ := rmw_window _ _ rfl hf hex hs ho
    have hw := window_rank (stepOne_dord _ hs ho).2.2.1 hb hr h1 h2
    have hx3 : o.thread.st.st.1.regs.X3.toBitVec = BitVec.setWidth 64 v := by rw [hst]; simp
    have hx : o.thread.st.st.1.regs.X2 = u.st.st.1.regs.X2 := hx2 (by decide) (by decide)
    have e18 : sOf 18 o.thread.st.st.1 = if BitVec.setWidth 64 v = u.st.st.1.regs.X2.toBitVec then 1 else 0 := by
      simp [sOf, hx3, hx]
    rw [show nextP 17 u.st.st.1 = 18 from rfl]
    by_cases hv : BitVec.setWidth 64 v = u.st.st.1.regs.X2.toBitVec
    · rw [ite_eq_left hv] at e18
      simp only [rk, e18, ↓reduceIte]; have := fl_le u.st.st.1 (curT t u mem); omega
    · rw [ite_eq_right hv] at e18
      simp only [rk, e18, Nat.zero_ne_one, ↓reduceIte]
      by_cases he : u.st.st.1.regs.X2.toBitVec = BitVec.setWidth 64 (curT t u mem)
      · have := hw.1 fun e => hv (by rw [e]; exact he.symm)
        rw [show fl u.st.st.1 (curT t u mem) = 0 from ite_eq_left he]
        simp only [topL] at hc hN3 this ⊢
        omega
      · rw [show fl u.st.st.1 (curT t u mem) = 10 from ite_eq_right he]
        simp only [topL] at hc hN3 ⊢
        omega
  · rw [show nextP 18 u.st.st.1 = 19 from rfl] at hSle ⊢
    simp only [rk]
    have := sOf_le 19 o.thread.st.st.1
    split <;> split <;> omega
  · by_cases hz : u.st.st.1.status.z = true <;> simp [nextP, rk, nextH, sOf, hz] <;> omega
  · rw [show nextP 20 u.st.st.1 = 21 from rfl]; simp [rk]
  · rw [show nextP 21 u.st.st.1 = 22 from rfl]; simp [rk]
  · rw [show nextP 22 u.st.st.1 = 24 from rfl]; simp [rk]
  · rw [stepOne_end' hS (by rw [hpc, (by unfold endP; split <;> simp_all [pcsR] : endP r = 24)])] at hs; cases hs

end Rank

/-! ## The cut of the empty spin -/

theorem get_set2_le (a : Array View) (x : View) : (a.setIfInBounds 2 x)[2]! ≤ x := by
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  split <;> (try split) <;> simp_all

theorem arrLe_set2 {a : Array View} {x : View} (h : (a[2]! : View) ≤ x) : ArrLe a (a.setIfInBounds 2 x) := by
  refine ⟨by simp, fun j => ?_⟩
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds] at h ⊢
  split
  · rename_i hj
    subst hj
    split
    · exact h
    · simp_all
  · exact Nat.le_refl _

/-- **The witness relation**: `cur` is `q` at another address, with the same
registers, register views, forwarding table, pending exclusive and promises,
and grown views. -/
structure Wit (q cur : Thread isa) : Prop where
  st : cur.st = goto q.st q.st.st.1 cur.st.st.2
  rv : cur.rview = q.rview
  wv : cur.wview = q.wview
  grow : q.views.Grow cur.views
  fwd : cur.views.fwdb = q.views.fwdb
  xclb : cur.views.xclb = q.views.xclb
  prom : cur.prom = q.prom

theorem Wit.refl (q : Thread isa) : Wit q q := ⟨rfl, rfl, rfl, Views.Grow.refl _, rfl, rfl, rfl⟩

/-- **The witness**: an earlier `CBZ` state `q` with `X2 = 0`, reached in
`a₁ ≤ a` steps with the current memory, whose `X2` views are at most its
`vrNew` (the `LDAR` that loaded `X2`), and related to the current thread. -/
def W (tid : Nat) (s0 : Thread isa) (mem0 : Memory) (a : Nat) (p : Thread isa × Memory) : Prop :=
  ∃ (q : Thread isa) (a₁ : Nat), a₁ ≤ a ∧ ThreadNPn Arch.armv8 tid a₁ (s0, mem0) (q, p.2) ∧
    q.st.st.2 = pcT 14 ∧ q.st.st.1.regs.X2.toBitVec = 0#64 ∧ (q.rview[2]! : View) ≤ q.views.vrNew ∧
    (q.wview[2]! : View) ≤ q.views.vrNew ∧ Wit q p.1

/-- **The cut**: an `LDAR` reading `0` from a loop head related to the
witness `q` reaches a state that `q` dominates, so the rest of the run
replays from `q`. -/
theorem cut_13 {ds : Decls} {t n : BitVec 64} {r tid a₁ k : Nat} {s0 q u : Thread isa} {mem0 mem : Memory}
    {outs : List (Except String (Outcome isa))} {oc : Outcome isa} {rr : Thread isa × Memory}
    (hS : Static ds t n r u.st) (hi : 13 ∈ pcsR r) (hT : ds.AgreesAt t 8) (hpc : u.st.st.2 = pcT 13)
    (hs : stepOne Arch.armv8 u tid mem = some outs) (ho : .ok oc ∈ outs)
    (hz : oc.thread.st.st.1.regs.X2.toBitVec = 0#64)
    (hq : ThreadNPn Arch.armv8 tid a₁ (s0, mem0) (q, mem)) (hq14 : q.st.st.2 = pcT 14)
    (hqz : q.st.st.1.regs.X2.toBitVec = 0#64) (hqr : (q.rview[2]! : View) ≤ q.views.vrNew)
    (hqw : (q.wview[2]! : View) ≤ q.views.vrNew) (hw : Wit q u)
    (hrun : ThreadNPn Arch.armv8 tid k (oc.thread, oc.mem) rr) (hp : rr.1.prom = []) :
    CertOkN Arch.armv8 tid s0 mem0 (a₁ + k) := by
  obtain ⟨v, c', ν, hm, hcp, hcx, hν1, hν2, hoc⟩ := step_13 hS hs ho hi hT hpc
  obtain ⟨hg, -, hnw⟩ := stepOne_grow Arch.armv8 hs ho
  have hst0 : oc.thread.st =
      goto u.st { u.st.st.1 with regs := u.st.st.1.regs.setXReg .X2 (BitVec.setWidth 64 v) } (pcT 14) := by
    rw [hoc]; rfl
  have hz' : BitVec.setWidth 64 v = 0#64 := by
    have hx : oc.thread.st.st.1.regs.X2.toBitVec = BitVec.setWidth 64 v := by rw [hst0]; simp
    rw [← hx, hz]
  have hst : oc.thread.st = q.st := by
    rw [hst0, hz', hw.st]
    show goto q.st { q.st.st.1 with regs := q.st.st.1.regs.setXReg .X2 0#64 } (pcT 14) = q.st
    rw [← hqz, CertBoundedSpinCas.setXReg_X2_self, ← hq14]
    rfl
  have hrv : oc.thread.rview = q.rview.setIfInBounds 2 ν := by
    rw [hoc]; show u.rview.set! 2 ν = _; rw [Array.set!_eq_setIfInBounds, hw.rv]
  have hwv : oc.thread.wview = q.wview.setIfInBounds 2 ν := by
    rw [hoc]; show u.wview.set! 2 ν = _; rw [Array.set!_eq_setIfInBounds, hw.wv]
  have hxc : oc.thread.views.xclb = q.views.xclb := by rw [hoc]; exact hcx.trans hw.xclb
  have hpr : oc.thread.prom = u.prom := by rw [hoc]; exact hcp
  have hfw : oc.thread.views.fwdb = u.views.fwdb := ((hnw (by rw [hm])).2 (by rw [hpr])).1
  have hle : q.views.vrNew ≤ ν := Nat.le_trans hw.grow.vrNew hν1
  have hd : q.Dom oc.thread :=
    ⟨hst.symm, by rw [hrv]; exact arrLe_set2 (Nat.le_trans hqr hle),
     by rw [hwv]; exact arrLe_set2 (Nat.le_trans hqw hle),
     (hw.grow.trans hg).dom (hfw.trans hw.fwd).symm hxc.symm, (hpr.trans hw.prom).symm⟩
  rw [hm] at hrun
  obtain ⟨r', hr', hdr, -⟩ := hrun.dom (q, mem) hd rfl
  exact ⟨r'.1, r'.2, hq.trans hr', hdr.prom.trans hp⟩

/-! ## Solo runs: a long run has a cut -/

section Loop

variable {ds : Decls} {t n : BitVec 64} (hT : ds.AgreesAt t 8) (hD : ds.AgreesAt n 4)
  (hN : ds.AgreesAt (n + 8#64) 8) (htn : t ≠ n + 8#64)
include hT hD hN htn

omit hT hD hN htn in
/-- The step invariant of a run of a thread (role `r`) alone. -/
def SoloP (ds : Decls) (t n : BitVec 64) (r : Nat) (p : Thread isa × Memory) : Prop :=
  Static ds t n r p.1.st ∧ PcOK r p.1.st ∧ Witness.FwdLeCoh p.1.views ∧ p.1.Bnd p.2.last ∧
    (∀ ts ∈ p.1.prom, ts ≤ p.2.last) ∧ p.2.cntBelow (topL t) p.2.last ≤ 2 + S p.1

/-- **A solo run is no longer than the rank, or a shorter certification
exists**: induction along the run, carrying the prefix length `a` and the
witness flag `h`. -/
theorem run_bound {r tid : Nat} {s0 : Thread isa} {mem0 : Memory} :
    ∀ (k : Nat) (p rr : Thread isa × Memory), ThreadRun Arch.armv8 tid k p rr → rr.1.prom = [] →
      ∀ (a : Nat) (h : Bool), ThreadNPn Arch.armv8 tid a (s0, mem0) p → SoloP ds t n r p →
      (h = true → W tid s0 mem0 a p) → k ≤ R h t p.1 p.2 ∨ ∃ m, m < a + k ∧ CertOkN Arch.armv8 tid s0 mem0 m := by
  intro k p rr hr
  induction hr with
  | refl p => intro _ _ _ _ _ _; exact .inl (Nat.zero_le _)
  | @step k p q rr hs rest ih =>
    intro hp a h hpre hSo hW
    obtain ⟨u, mem⟩ := p
    simp only [SoloP] at hSo
    dsimp only at hW hpre ⊢
    obtain ⟨outs, oc, hs, ho, rfl⟩ := hs
    dsimp only at hs
    obtain ⟨hS, hP, hf, hb, hpl, hc⟩ := hSo
    obtain ⟨qk, hpl', -, -, hc'⟩ := solo_step hT hD hN htn hS hP hpl hs ho
    have hS2 : S oc.thread ≤ 1 := sOf_le _ _
    have hSo' : SoloP ds t n r (oc.thread, oc.mem) :=
      ⟨qk.st, qk.pc, Witness.stepOne_fwdLeCoh hs ho hf, (stepOne_bnd _ hs ho hb).1, hpl', by dsimp only; omega⟩
    have hN3 : cntT t oc.thread oc.mem ≤ 3 := by
      have := cntBelow_le_last oc.mem (topL t) (oc.thread.views.getCoh (topL t))
      simp only [cntT]; omega
    have hpre' : ThreadNPn Arch.armv8 tid (a + 1) (s0, mem0) (oc.thread, oc.mem) :=
      hpre.tail ⟨outs, oc, hs, ho, rfl⟩
    obtain ⟨i, hi, hpc, hI⟩ := id hP
    have hpu : pos u = i := by rw [pos, hpc, posOf_pcT (mem_tPcs hi)]
    by_cases hcut : i = 13 ∧ h = true ∧ oc.thread.st.st.1.regs.X2.toBitVec = 0#64
    · obtain ⟨rfl, rfl, hz⟩ := hcut
      obtain ⟨q, a₁, ha, hq, hq14, hqz, hqr, hqw, hw⟩ := hW rfl
      exact .inr ⟨a₁ + k, by omega, cut_13 hS hi hT hpc hs ho hz hq hq14 hqz hqr hqw hw rest.toNPn hp⟩
    · have hlt := rank_step hT hD hN htn hS hP hs ho hf (hb.views.le.coh (topL t)) hN3 (h := h)
        (fun h1 h2 h3 => hcut ⟨by omega, h2, h3⟩)
      have hW' : nextH (pos u) u.st.st.1 oc.thread.st.st.1 h = true →
          W tid s0 mem0 (a + 1) (oc.thread, oc.mem) := by
        rw [hpu]
        intro hh
        by_cases h13 : i = 13
        · subst h13
          have hz : oc.thread.st.st.1.regs.X2.toBitVec = 0#64 := of_decide_eq_true hh
          obtain ⟨v, c', ν, hm, hcp, hcx, hν1, hν2, hoc⟩ := step_13 hS hs ho hi hT hpc
          refine ⟨oc.thread, a + 1, Nat.le_refl _, hpre', by rw [hoc]; rfl, hz, ?_, ?_, Wit.refl _⟩
          · rw [hoc]; show (u.rview.set! 2 ν)[2]! ≤ c'.views.vrNew
            rw [Array.set!_eq_setIfInBounds]; exact Nat.le_trans (get_set2_le _ _) hν2
          · rw [hoc]; show (u.wview.set! 2 ν)[2]! ≤ c'.views.vrNew
            rw [Array.set!_eq_setIfInBounds]; exact Nat.le_trans (get_set2_le _ _) hν2
        · by_cases h14 : i = 14
          · subst h14
            have hh' : h = true ∧ u.st.st.1.regs.X2.toBitVec = 0#64 := by
              simpa only [nextH, show (14 = 13) = False by decide, ↓reduceIte, Bool.and_eq_true,
                decide_eq_true_eq] using hh
            obtain ⟨rfl, hz⟩ := hh'
            obtain ⟨q, a₁, ha, hq, hq14, hqz, hqr, hqw, hw⟩ := hW rfl
            obtain ⟨hm, hpr, hst, hrv, hwv, hxc, hg, hfw⟩ := step_14 hS hs ho hi hpc
            rw [ite_eq_left hz] at hst
            refine ⟨q, a₁, by omega, by rw [hm]; exact hq, hq14, hqz, hqr, hqw, ⟨?_, hrv.trans hw.rv, hwv.trans hw.wv,
              hw.grow.trans hg, hfw.trans hw.fwd, hxc.trans hw.xclb, hpr.trans hw.prom⟩⟩
            rw [hst, hw.st]
          · simp only [nextH, h13, h14, ↓reduceIte, Bool.false_eq_true] at hh
      rcases ih hp (a + 1) _ hpre' hSo' hW' with hb' | ⟨m, hm, hc⟩
      · exact .inl (by simp only at hb' ⊢; omega)
      · exact .inr ⟨m, by omega, hc⟩

/-- **Every certification of a thread under `SoloP` is within `51`
instructions.** -/
theorem certOkN_bound {r tid : Nat} {u : Thread isa} {mem : Memory} (hSo : SoloP ds t n r (u, mem)) {k : Nat}
    (h : CertOkN Arch.armv8 tid u mem k) : CertOkN Arch.armv8 tid u mem 51 := by
  refine CertOkN.bound_of_shorter 51 (fun k rr hr hp hk => ?_) h
  rcases run_bound hT hD hN htn k (u, mem) rr hr hp 0 false (.refl _ _) hSo (fun h => Bool.noConfusion h) with
    hb | ⟨m, hm, hc⟩
  · exact absurd (Nat.le_trans hb (rk_le _ _ _ _ _)) (by omega)
  · exact ⟨m, by omega, hc⟩

end Loop

/-! ## Bounded certification -/

section Bound

variable {ds : Decls} {t n : BitVec 64} (hT : ds.AgreesAt t 8) (hD : ds.AgreesAt n 4)
  (hN : ds.AgreesAt (n + 8#64) 8) (htn : t ≠ n + 8#64)

/-- A thread of an `Inv ∧ InvH` configuration runs alone under `SoloP`: at
most `2` writes to `top` (each thread's `S + promAt top ≤ 1`). -/
theorem soloP_of_inv {fuel : Nat} {c : Config isa} (hI : Inv ds t n fuel c) (hH : InvH t c) {tid : Nat}
    {u : Thread isa} (hu : c.threads[tid]? = some u) : SoloP ds t n tid (u, c.mem) := by
  have hTI := hI.thr tid u hu
  have hsum : tsum c (fun _ u => S u + c.mem.promAt (topL t) u.prom) ≤ c.threads.size * 1 :=
    tsum_le fun i v hv => (hH i v hv).2
  have := hI.cnt
  rw [hI.size] at hsum
  exact ⟨hTI.st, hTI.pc, (hH tid u hu).1, hI.bnd tid u hu, hTI.promLe, by dsimp only; omega⟩

include hT hD hN htn in
/-- **Bounded certification from any configuration with `Inv` at every fuel
and `InvH`** (semantic machine): `F = 51`. -/
theorem treiber_pp_certBounded_gen {c0 : Config isa} (h0 : ∀ fuel, Inv ds t n fuel c0) (hH0 : InvH t c0) :
    CertBoundedFrom Arch.armv8 c0 51 := by
  intro fuel c hr tid u k hu hc
  have hI := NoStuck.reachableSem_inv (fun c => Inv ds t n fuel c ∧ InvH t c)
    (fun _ c _ hc hst => ⟨by obtain ⟨u, hu⟩ := TreiberPp.stepSem_get hst; exact hc.1.step hT hD hN htn hu hst,
      InvH.step hT hD hN htn hc.1 hc.2 hst⟩) hr ⟨h0 fuel, hH0⟩
  exact certOkN_bound hT hD hN htn (soloP_of_inv hI.1 hI.2 hu) hc

end Bound

section Headlines
open Kraken.Promising.SLR.EnvG.Treiber (StartPushW StartPopW StartPushWD StartPopWD treiberSA)

/-- **Bounded certification for `treiber_pp.kl`** (no declarations): from
the start configurations of `treiber_pp_live_sem`, every certification of a
reachable thread, at every fuel, fits in `51` instructions. -/
theorem treiber_pp_certBounded (l : _root_.Layout) [Executable.ValidLayout (l treiberImageA)]
    (t n : BitVec 64) (htn : t ≠ n + 8) {sP sQ : isa.State} {initMem : List (Loc × Val)}
    (hP : StartPushW (layout := l) t n sP) (hQ : StartPopW (layout := l) t sQ) :
    CertBoundedFrom Arch.armv8 (Config.init [sP, sQ] initMem : Config isa) 51 := by
  have hP' : StartPushWD (layout := l) {} t n sP := ⟨hP.exe, hP.decls, hP.pc, hP.endPc, hP.x0, hP.x1, hP.x9, hP.dt,
    hP.dd, hP.dn⟩
  have hQ' : StartPopWD (layout := l) {} t sQ := ⟨hQ.exe, hQ.decls, hQ.pc, hQ.endPc, hQ.x0, hQ.dt, hQ.d4⟩
  have hE := fun a k => Decls.agreesAt_empty a k
  exact treiber_pp_certBounded_gen (layout := l) (hE _ _) (hE _ _) (hE _ _) htn
    (fun _ => Inv.init (start0 hP').1 (start0 hP').2 (start1 (n := n) hQ').1 (start1 (n := n) hQ').2) InvH.init

/-- **Bounded certification for `treiber_pp.kl` with the runner's
declarations**: from the start configurations of `treiber_pp_live_runner`,
`F = 51`. -/
theorem treiber_pp_certBounded_runner (l : _root_.Layout) [Executable.ValidLayout (l treiberImageA)]
    {ds : Decls} (t n : BitVec 64) (hag : ds.AgreesOnA (treiberSA t n)) (htn : t ≠ n + 8)
    {sP sQ : isa.State} {initMem : List (Loc × Val)} (hP : StartPushWD (layout := l) ds t n sP)
    (hQ : StartPopWD (layout := l) ds t sQ) :
    CertBoundedFrom Arch.armv8 (Config.init [sP, sQ] initMem : Config isa) 51 :=
  treiber_pp_certBounded_gen (layout := l) (hag (t, 8) (by simp)) (hag (n, 4) (by simp)) (hag (n + 8, 8) (by simp))
    htn (fun _ => Inv.init (start0 hP).1 (start0 hP).2 (start1 (n := n) hQ).1 (start1 (n := n) hQ).2) InvH.init

/-- **`treiber_pp.kl` is live on the fuel-free semantic machine**: from the
start configurations of `treiber_pp_live_sem`, on every fuel-free trace that
is weakly fair and memory fair, the pusher and the popper both reach their
end addresses. No extra hypothesis: `treiber_pp_live_sem` at fuel `51`,
transferred by `treiber_pp_certBounded`. -/
theorem treiber_pp_live_semU (l : _root_.Layout) [Executable.ValidLayout (l treiberImageA)]
    (t n : BitVec 64) (htn : t ≠ n + 8) (hn : n ≠ 0) {sP sQ : isa.State} {initMem : List (Loc × Val)}
    (hP : StartPushW (layout := l) t n sP) (hQ : StartPopW (layout := l) t sQ)
    (hT0 : (Config.init [sP, sQ] initMem).mem.initVal ⟨t, 8⟩ = 0) :
    LiveFromSemU Arch.armv8 (Config.init [sP, sQ] initMem)
      (fun cfg => WeakFairSemU Arch.armv8 cfg ∧ MemFair Arch.armv8 cfg) (fun tid _ => tid < 2) Done :=
  liveTransfer (treiber_pp_certBounded l t n htn hP hQ) (treiber_pp_live_sem l t n htn hn hP hQ hT0)

/-- **`treiber_pp.kl` with the runner's declarations is live on the
fuel-free semantic machine**: `treiber_pp_live_runner` at fuel `51`,
transferred by `treiber_pp_certBounded_runner`. -/
theorem treiber_pp_live_runner_semU (l : _root_.Layout) [Executable.ValidLayout (l treiberImageA)]
    {ds : Decls} (hsz : ds.StrictSized) (t n : BitVec 64) (hag : ds.AgreesOnA (treiberSA t n)) (htn : t ≠ n + 8)
    (hn : n ≠ 0) {sP sQ : isa.State} {initMem : List (Loc × Val)} (hP : StartPushWD (layout := l) ds t n sP)
    (hQ : StartPopWD (layout := l) ds t sQ) (hdnQ : Mem.loadInt sQ.st.1.dmem (n + 8) 8 = none)
    (hT0 : (Config.init [sP, sQ] initMem).mem.initVal ⟨t, 8⟩ = 0)
    (hN0 : (Config.init [sP, sQ] initMem).mem.initVal ⟨n + 8, 8⟩ = 0) :
    LiveFromSemU Arch.armv8 (Config.init [sP, sQ] initMem)
      (fun cfg => WeakFairSemU Arch.armv8 cfg ∧ MemFair Arch.armv8 cfg) (fun tid _ => tid < 2) Done :=
  liveTransfer (treiber_pp_certBounded_runner l t n hag htn hP hQ)
    (treiber_pp_live_runner l hsz t n hag htn hn hP hQ hdnQ hT0 hN0)

section
open Kraken.Promising.SLR.EnvG.Treiber Kraken.Promising.SLR.EnvG.ConcreteTreiber

/-- `treiber_pp_live_semU` at the runner's configuration
(`[pusherW0, popperW1]`, `wLayoutT`, `treiberInitMem`), no hypotheses. -/
theorem treiber_pp_live_semU_concrete :
    LiveFromSemU Arch.armv8 (Config.init [pusherW0, popperW1] treiberInitMem)
      (fun cfg => WeakFairSemU Arch.armv8 cfg ∧ MemFair Arch.armv8 cfg) (fun tid _ => tid < 2) Done :=
  liveTransfer (treiber_pp_certBounded wLayoutT topAddr n1Addr (by decide) pusherW0_start popperW1_start)
    (treiber_pp_live_sem_concrete 51)

/-- `treiber_pp_live_runner_semU` at the runner's exact configuration
(`[pusherWD0, popperWD1]`, `treiberDeclsD`, `wLayoutT`, `treiberInitMem`), no
hypotheses. -/
theorem treiber_pp_live_runner_semU_concrete :
    LiveFromSemU Arch.armv8 (Config.init [pusherWD0, popperWD1] treiberInitMem)
      (fun cfg => WeakFairSemU Arch.armv8 cfg ∧ MemFair Arch.armv8 cfg) (fun tid _ => tid < 2) Done :=
  have hag : treiberDeclsD.AgreesOnA (treiberSA topAddr n1Addr) := by decls_agrees_on_a
  liveTransfer (treiber_pp_certBounded_runner wLayoutT topAddr n1Addr hag (by decide) pusherWD0_start
    popperWD1_start) (treiber_pp_live_runner_concrete 51)

end

end Headlines

end Kraken.Promising.Live.CertBoundedTreiberPpA64

#print axioms Kraken.Promising.Live.CertBoundedTreiberPpA64.treiber_pp_certBounded
#print axioms Kraken.Promising.Live.CertBoundedTreiberPpA64.treiber_pp_certBounded_runner
#print axioms Kraken.Promising.Live.CertBoundedTreiberPpA64.treiber_pp_live_semU
#print axioms Kraken.Promising.Live.CertBoundedTreiberPpA64.treiber_pp_live_semU_concrete
#print axioms Kraken.Promising.Live.CertBoundedTreiberPpA64.treiber_pp_live_runner_semU
#print axioms Kraken.Promising.Live.CertBoundedTreiberPpA64.treiber_pp_live_runner_semU_concrete
