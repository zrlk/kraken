/-
**F3: the holder of the served ticket certifies without
fresh writes** (repeated-acquire ticket lock `tkLoopWorker`, semantic machine:
`TraceSem`, `CertOkN`, `NACertG`).

`HoldsLoop x u mem M`: thread `u` holds ticket `M`, taken (positions 6–13
with `tk u = M`) or reserved (an outstanding promise of `next := M + 1`).
`holder_nacert`: on a semantic trace from a start configuration, if `u` holds
`M`, no message of `owner := M + 1` exists and `u` is certifiable, then `u`
has no promise or certifies without any fresh write (`NACertG`), which
replays against every larger memory (`nacertG_replay`).

**Why** (the three model facts of `LiveTicketLoopFacts.lean`): cut any
certification at its first empty promise set; no fresh write happens before.
While the holder still holds `M` (`Phase`: taken with `tk = M`, or the
`next := M + 1` promise outstanding) and has a promise:

- its round-`M` `STLR` writes `owner := M + 1`, so it cannot fulfil (no such
  message) and is fresh;
- a fresh write at `θ = |M| + 1` leaves some older promise `p < θ`
  outstanding forever (`Win`): a fresh `LDADDA` raises `coh next` to `θ` (only
  in the reserved case, where `p` is the `next` promise); a fresh `STR` raises
  `vwOld` to `θ`, so the next `STLR` (a release: fact 1) fulfils nothing below
  `θ` and raises `vRel` above it; a fresh `STLR` raises `vRel` to `θ`; the next
  `LDADDA` (an acquire: facts 2 and 3) then fulfils nothing below `vRel` and
  raises `vwNew` to it, and a promise at or below `vwNew` is dead (`DeadW`).

So every certification of the holder, cut at its first empty promise set, has
no fresh write (`phase_run`).

**Hypotheses beyond the trace** (prototype, `holder_nacert`): `hM32 : M + 1 < 2 ^ 32`
(the served ticket does not wrap). The trace invariant with promises must
provide it (`owner ≤ next ≤ N * k`). Everything else comes from the trace:
`SInv` (`trace_sinv`), the worker's own register facts (`RegInv`,
`trace_reginv`), and `Config.Wf` (`trace_wf`). The hypothesis `hM` (`owner`'s
final value is `M`) is not needed.
-/
import Kraken.Promising.LiveTicketLoopInv
import Kraken.Promising.LiveTicketLoopFacts

namespace Kraken.Promising.Live.TicketLoopHolder

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live Kraken.Promising.Live.Sem
open Kraken.Promising.Live.TicketLoop Kraken.Promising.Live.TicketLoopTrees Kraken.Promising.Live.TicketLoopStatic
open Kraken.Promising.Live.TicketLoopInv
open Kraken.Promising.Live.TicketStep Kraken.Promising.Live.SemShape Kraken.Promising.Live.LoopFacts
open Kraken.Promising.Live.TicketInv (wn L4)
open Kraken.Promising.Live.TicketTrees (w32)
open Kraken.Promising.SLR.A64Trees (goto)

set_option linter.unusedSectionVars false

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout tkLoopWorker)]

set_option hygiene false in
local notation "pcA" => (layout tkLoopWorker).addrOf

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

theorem pc_ne {s : isa.State} {i j : Nat} (hi : s.st.2 = pcA i) (hj : s.st.2 = pcA j) (hi' : i ∈ tkLoopPcs)
    (hj' : j ∈ tkLoopPcs) (h : i ≠ j) : False :=
  h (addrOf_inj hi' hj' (hi.symm.trans hj))

theorem wn_setWidth' (v : BitVec 128) : wn (UInt64.ofBitVec (BitVec.setWidth 64 (BitVec.setWidth 32 v))) =
    v.toNat % 2 ^ 32 := TicketInv.wn_setWidth32 v

theorem val_setWidth' (r : UInt64) : (BitVec.setWidth 128 (BitVec.setWidth 32 r.toBitVec)).toNat = wn r :=
  TicketInv.val_setWidth32 r

/-! ## The worker's own register facts -/

/-- **The register facts a worker establishes for itself**: `X6 = 1` past its
`MOV`, and `X4 = X3 + 1` (low words) at its `STLR`. -/
structure RegInv (s : isa.State) : Prop where
  x6 : s.st.2 = pcA 1 ∨ wn s.st.1.regs.X6 = 1
  x4 : s.st.2 = pcA 13 → wn s.st.1.regs.X4 = (wn s.st.1.regs.X3 + 1) % 2 ^ 32

theorem RegInv.x6' {s : isa.State} (h : RegInv s) {i : Nat} (hi : i ∈ tkLoopPcs) (hpc : s.st.2 = pcA i)
    (h1 : i ≠ 1) : wn s.st.1.regs.X6 = 1 :=
  h.x6.resolve_left fun e => pc_ne hpc e hi (by decide) h1

theorem regInv_of {s : isa.State} {j : Nat} (hj : j ∈ tkLoopPcs) (hpc : s.st.2 = pcA j)
    (h6 : wn s.st.1.regs.X6 = 1) (h13 : j ≠ 13) : RegInv s :=
  ⟨.inr h6, fun h => (pc_ne hpc h hj (by decide) h13).elim⟩

/-- `ADD W4, W3, #1` sets the low word of `X4` to the low word of `X3` plus one. -/
theorem wn_add4 (r : UInt64) :
    (BitVec.setWidth 64 (r.toBitVec.take 32 + 1#32)).toNat % 2 ^ 32 = (wn r + 1) % 2 ^ 32 := by
  simp only [wn, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.take, BitVec.extractLsb'_toNat,
    Nat.shiftRight_zero, BitVec.toNat_ofNat, UInt64.toNat]
  omega

/-- **One instruction step keeps `RegInv`**, with any promise set. -/
theorem step_reginv {x o c : BitVec 64} {t : Thread isa} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Outcome isa))} {oc : Outcome isa} (h : SInv x o c t.st) (hR : RegInv t.st)
    (hs : stepOne Arch.armv8 t tid mem = some outs) (ho : .ok oc ∈ outs) : RegInv oc.thread.st := by
  obtain ⟨hS, i, hi, hpc⟩ := h
  have hi' := hi
  simp only [tkLoopPcs, List.mem_cons, List.not_mem_nil, or_false] at hi'
  rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨-, hst, -, -⟩ := s1 hS hs ho hpc
    exact regInv_of (j := 3) (by decide) (by rw [hst] <;> rfl) (by rw [hst]; rfl) (by decide)
  · obtain ⟨-, hst, -, -⟩ := s3 hS hs ho hpc
    have h6 := hR.x6' hi hpc (by decide)
    by_cases hz : w32 t.st.st.1.regs.X7 = 0#32
    · rw [ite_eq_left hz] at hst
      exact regInv_of (j := 17) (by decide) (by rw [hst] <;> rfl) (by rw [hst]; exact h6) (by decide)
    · rw [ite_eq_right hz] at hst
      exact regInv_of (j := 4) (by decide) (by rw [hst] <;> rfl) (by rw [hst]; exact h6) (by decide)
  · obtain ⟨old, hst, -⟩ := TicketDrop.spec_rmw_len _ _ rfl
      (exec_ldadda _ (hS.at (by decide) (by decide) hpc) hS.x0 hS.dx) hs ho
    have h6 := hR.x6' hi hpc (by decide)
    exact regInv_of (j := 6) (by decide) (by rw [hst] <;> rfl) (by rw [hst]; exact h6) (by decide)
  · obtain ⟨ts, v, hst, -⟩ := s6 hS hs ho hpc
    have h6 := hR.x6' hi hpc (by decide)
    exact regInv_of (j := 7) (by decide) (by rw [hst] <;> rfl) (by rw [hst]; exact h6) (by decide)
  · obtain ⟨sf, hst, -⟩ := s7 hS hs ho hpc
    have h6 := hR.x6' hi hpc (by decide)
    exact regInv_of (j := 8) (by decide) (by rw [hst] <;> rfl) (by rw [hst]; exact h6) (by decide)
  · obtain ⟨-, hst, -, -⟩ := s8 hS hs ho hpc
    have h6 := hR.x6' hi hpc (by decide)
    by_cases hz : t.st.st.1.status.z = true
    · rw [ite_eq_left hz] at hst
      exact regInv_of (j := 9) (by decide) (by rw [hst] <;> rfl) (by rw [hst]; exact h6) (by decide)
    · rw [ite_eq_right hz] at hst
      exact regInv_of (j := 6) (by decide) (by rw [hst] <;> rfl) (by rw [hst]; exact h6) (by decide)
  · obtain ⟨v, hst, -⟩ := s9 hS hs ho hpc
    have h6 := hR.x6' hi hpc (by decide)
    exact regInv_of (j := 10) (by decide) (by rw [hst] <;> rfl) (by rw [hst]; exact h6) (by decide)
  · obtain ⟨-, hst, -, -⟩ := s10 hS hs ho hpc
    have h6 := hR.x6' hi hpc (by decide)
    exact regInv_of (j := 11) (by decide) (by rw [hst] <;> rfl) (by rw [hst]; exact h6) (by decide)
  · obtain ⟨hst, -⟩ := TicketDrop.spec_store_len _ _ (exec_str_c _ (hS.at (by decide) (by decide) hpc) hS.x2 hS.dc)
      hs ho
    have h6 := hR.x6' hi hpc (by decide)
    exact regInv_of (j := 12) (by decide) (by rw [hst] <;> rfl) (by rw [hst]; exact h6) (by decide)
  · obtain ⟨-, hst, -, -⟩ := s12 hS hs ho hpc
    have h6 := hR.x6' hi hpc (by decide)
    refine ⟨.inr (by rw [hst]; exact h6), fun _ => ?_⟩
    rw [hst]
    exact wn_add4 _
  · obtain ⟨hst, -⟩ := TicketDrop.spec_store_len _ _ (exec_stlr _ (hS.at (by decide) (by decide) hpc) hS.x1 hS.dO)
      hs ho
    have h6 := hR.x6' hi hpc (by decide)
    exact regInv_of (j := 14) (by decide) (by rw [hst] <;> rfl) (by rw [hst]; exact h6) (by decide)
  · obtain ⟨-, hst, -, -⟩ := s14 hS hs ho hpc
    have h6 := hR.x6' hi hpc (by decide)
    exact regInv_of (j := 15) (by decide) (by rw [hst] <;> rfl) (by rw [hst]; exact h6) (by decide)
  · obtain ⟨-, hst, -, -⟩ := s15 hS hs ho hpc
    have h6 := hR.x6' hi hpc (by decide)
    exact regInv_of (j := 3) (by decide) (by rw [hst] <;> rfl) (by rw [hst]; exact h6) (by decide)
  · rw [stepOne_end hS hpc] at hs; cases hs

/-- **`RegInv` at every thread of every index** of a semantic trace from a
start configuration. -/
theorem trace_reginv {fuel k N : Nat} {x o c : BitVec 64} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : TkLoopStart k N x o c states initMem) (tr : TraceSem Arch.armv8 fuel isa)
    (h0 : tr.cfg 0 = Config.init states initMem) :
    ∀ i (tid : Nat) t, (tr.cfg i).threads[tid]? = some t → RegInv t.st
  | 0, tid, t, ht => by
    rw [h0] at ht
    simp only [Config.init, List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at ht
    obtain ⟨s, hs', rfl⟩ := ht
    have hpc : (Thread.init s : Thread isa).st.st.2 = pcA 1 :=
      ((hs.hst s (List.mem_of_getElem? hs')).pc).trans addrOf_0
    exact ⟨.inl hpc, fun h => (pc_ne hpc h (by decide) (by decide) (by decide)).elim⟩
  | i + 1, tid, t, ht => by
    have ih := trace_reginv hs tr h0 i
    rcases tr.step i with ⟨j, hst⟩ | ⟨-, he⟩
    · rcases stepSem_get hst ht with ⟨u, hu, e⟩ | ⟨u, outs, oc, hu, hso, ho, rfl⟩
      · have := ih tid u hu; rw [← e] at this; exact this
      · exact step_reginv (trace_sinv hs tr h0 i tid u hu) (ih tid u hu) hso ho
    · rw [he] at ht; exact ih tid t ht

omit layout hv in
/-- **Every configuration of a semantic trace from `Config.init` is well
formed** (`Config.Wf`: forwarding entries are the thread's own writes, and
outstanding promises are timestamps of memory). -/
theorem trace_wf {fuel : Nat} {states : List isa.State} {initMem : List (Loc × Val)}
    (tr : TraceSem Arch.armv8 fuel isa) (h0 : tr.cfg 0 = Config.init states initMem) : ∀ i, (tr.cfg i).Wf
  | 0 => h0 ▸ Config.init_wf _ _
  | i + 1 => by
    rcases tr.step i with ⟨tid, ⟨t, outs, oc, ht, hs, ho, -, he⟩ | ⟨t, w, ht, -, -, he⟩⟩ | ⟨-, he⟩
    · rw [he]; exact (trace_wf tr h0 i).instr ht hs ho
    · rw [he]; exact (trace_wf tr h0 i).promise ht w
    · rw [he]; exact trace_wf tr h0 i

/-! ## After a fresh write: an older promise is never fulfilled -/

/-- **After a fresh write at `θ`, an older promise `p < θ` stays outstanding**:
it is dead (`DeadW`), or the thread is before its `STLR` with `vwOld ≥ θ`
(positions 12, 13), or before its `LDADDA` with `vRel ≥ θ` (positions 14, 15,
3, 4, or at the end). -/
structure Win (x o c : BitVec 64) (θ : Time) (t : Thread isa) (m : Memory) : Prop where
  sinv : SInv x o c t.st
  le : θ ≤ m.last + 1
  ex : ∃ p ∈ t.prom, p < θ ∧ (DeadW t m p ∨ ((t.st.st.2 = pcA 12 ∨ t.st.st.2 = pcA 13) ∧ θ ≤ t.views.vwOld) ∨
    ((t.st.st.2 = pcA 14 ∨ t.st.st.2 = pcA 15 ∨ t.st.st.2 = pcA 3 ∨ t.st.st.2 = pcA 4 ∨ t.st.st.2 = pcA 17) ∧
      θ ≤ t.views.vRel))

/-- **`Win` is kept by every step.** -/
theorem win_step {x o c : BitVec 64} {θ : Time} {t : Thread isa} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Outcome isa))} {oc : Outcome isa} (h : Win x o c θ t mem)
    (hs : stepOne Arch.armv8 t tid mem = some outs) (ho : .ok oc ∈ outs) : Win x o c θ oc.thread oc.mem := by
  have hsinv := (step_sinv h.sinv hs ho).1
  obtain ⟨-, -, hpre, -⟩ := stepOne_dord Arch.armv8 hs ho
  have hle : θ ≤ oc.mem.last + 1 := Nat.le_trans h.le (Nat.succ_le_succ hpre.last_le)
  obtain ⟨⟨hS, i, hi, hpc⟩, hle0, p, hp, hlt, hk⟩ := h
  rcases hk with hd | ⟨hpc', hvw⟩ | ⟨hpc', hvr⟩
  · have hd' := deadW_step Arch.armv8 hs ho hd
    exact ⟨hsinv, hle, p, hd'.1, hlt, .inl hd'⟩
  · rcases hpc' with hpc' | hpc'
    · obtain ⟨-, hst, hpr, -⟩ := s12 hS hs ho hpc'
      have hv := spec_done_vw _ _ (exec_add4 _ (hS.at (by decide) (by decide) hpc')) hs ho
      exact ⟨hsinv, hle, p, hpr ▸ hp, hlt, .inr (.inl ⟨.inr (by rw [hst] <;> rfl), hv ▸ hvw⟩)⟩
    · obtain ⟨hst, hw⟩ := spec_store_rel _ _ rfl (exec_stlr _ (hS.at (by decide) (by decide) hpc') hS.x1 hS.dO) hs ho
      have hpc2 : oc.thread.st.st.2 = pcA 14 := by rw [hst] <;> rfl
      rcases hw with ⟨-, hpr, hvr⟩ | ⟨ts, -, -, hvo, -, hpr, hvr⟩
      · refine ⟨hsinv, hle, p, ?_, hlt, .inr (.inr ⟨.inl hpc2, by omega_t⟩)⟩
        rw [hpr]
        exact (List.mem_erase_of_ne (by omega_t)).mpr (List.mem_append_left _ hp)
      · refine ⟨hsinv, hle, p, ?_, hlt, .inr (.inr ⟨.inl hpc2, by omega_t⟩)⟩
        rw [hpr]
        exact (List.mem_erase_of_ne (by omega_t)).mpr hp
  · rcases hpc' with hpc' | hpc' | hpc' | hpc' | hpc'
    · obtain ⟨-, hst, hpr, -⟩ := s14 hS hs ho hpc'
      have hv := spec_done_vRel _ _ (exec_sub _ (hS.at (by decide) (by decide) hpc')) hs ho
      exact ⟨hsinv, hle, p, hpr ▸ hp, hlt, .inr (.inr ⟨.inr (.inl (by rw [hst] <;> rfl)), hv ▸ hvr⟩)⟩
    · obtain ⟨-, hst, hpr, -⟩ := s15 hS hs ho hpc'
      have hv := spec_done_vRel _ _ (exec_b_round _ (hS.at (by decide) (by decide) hpc')) hs ho
      exact ⟨hsinv, hle, p, hpr ▸ hp, hlt, .inr (.inr ⟨.inr (.inr (.inl (by rw [hst] <;> rfl))), hv ▸ hvr⟩)⟩
    · obtain ⟨-, hst, hpr, -⟩ := s3 hS hs ho hpc'
      have hv := spec_done_vRel _ _ (exec_cbz _ (hS.at (by decide) (by decide) hpc')) hs ho
      by_cases hz : w32 t.st.st.1.regs.X7 = 0#32
      · rw [ite_eq_left hz] at hst
        exact ⟨hsinv, hle, p, hpr ▸ hp, hlt,
          .inr (.inr ⟨.inr (.inr (.inr (.inr (by rw [hst] <;> rfl)))), hv ▸ hvr⟩)⟩
      · rw [ite_eq_right hz] at hst
        exact ⟨hsinv, hle, p, hpr ▸ hp, hlt,
          .inr (.inr ⟨.inr (.inr (.inr (.inl (by rw [hst] <;> rfl)))), hv ▸ hvr⟩)⟩
    · obtain ⟨hvw, hful⟩ := spec_rmw_acq _ _ rfl rfl
        (exec_ldadda _ (hS.at (by decide) (by decide) hpc') hS.x0 hS.dx) hs ho
      have hin : p ∈ oc.thread.prom := Classical.byContradiction fun hn => by
        have := hful p hp hn; omega_t
      exact ⟨hsinv, hle, p, hin, hlt, .inl ⟨hin, .inl (by omega_t)⟩⟩
    · rw [stepOne_end hS hpc'] at hs; cases hs

/-- **A thread in `Win` never empties its promise set.** -/
theorem win_run {x o c : BitVec 64} {θ : Time} {tid : Nat} : ∀ {n : Nat} {p q : Thread isa × Memory},
    ThreadNPn Arch.armv8 tid n p q → Win x o c θ p.1 p.2 → q.1.prom ≠ [] := by
  intro n p q h
  induction h with
  | refl => intro hW he; obtain ⟨p, hp, -⟩ := hW.ex; rw [he] at hp; exact absurd hp (by simp)
  | step hs _ ih =>
    intro hW
    obtain ⟨outs, oc, hs, ho, rfl⟩ := hs
    exact ih (win_step hW hs ho)

/-! ## Before the first fresh write: the holder keeps holding `M` -/

/-- **The holder of ticket `M`, before any fresh write**: `SInv`, `RegInv`,
the `Config.Wf` facts, no `owner := M + 1` message, and `M` taken (`tk = M`
at positions 6–13) or reserved (the `next := M + 1` promise outstanding). -/
structure Phase (x o c : BitVec 64) (M : Nat) (t : Thread isa) (m : Memory) : Prop where
  sinv : SInv x o c t.st
  reg : RegInv t.st
  fwd : t.views.FwdOk
  wf : ∀ p ∈ t.prom, p ≤ m.last
  hno : ∀ ts w, m.get? ts = some w → w.loc = L4 o → w.val.toNat ≠ M + 1
  hold : (Ticketed t ∧ tk t = M) ∨ ∃ ts ∈ t.prom, ∃ w, m.get? ts = some w ∧ w.loc = L4 x ∧ w.val.toNat = M + 1

section PhaseStep

variable {x o c : BitVec 64} {M : Nat} (hxo : L4 x ≠ L4 o) (hxc : L4 x ≠ L4 c) (hM32 : M + 1 < 2 ^ 32)

/-- A step that keeps memory and promises and keeps a taken ticket keeps
`Phase`. -/
theorem phase_quiet {t : Thread isa} {tid : Nat} {mem : Memory} {outs : List (Except String (Outcome isa))}
    {oc : Outcome isa} (h : Phase x o c M t mem) (hs : stepOne Arch.armv8 t tid mem = some outs)
    (ho : .ok oc ∈ outs) (hm : oc.mem = mem) (hpr : oc.thread.prom = t.prom)
    (htk : Ticketed t ∧ tk t = M → Ticketed oc.thread ∧ tk oc.thread = M) : Phase x o c M oc.thread oc.mem := by
  obtain ⟨-, -, hf', -, -, hp'⟩ := stepOne_silent_nt Arch.armv8 hs ho h.fwd
  refine ⟨(step_sinv h.sinv hs ho).1, step_reginv h.sinv h.reg hs ho, hf', hp' h.wf, hm ▸ h.hno, ?_⟩
  rcases h.hold with h1 | ⟨ts, hts, w, hw, h2⟩
  · exact .inl (htk h1)
  · exact .inr ⟨ts, hpr ▸ hts, w, hm ▸ hw, h2⟩

include hxo hxc hM32

/-- **One step of the holder with a promise**: it keeps memory and `Phase`, or
it is a fresh write after which an older promise is never fulfilled. -/
theorem phase_step {t : Thread isa} {tid : Nat} {mem : Memory} {outs : List (Except String (Outcome isa))}
    {oc : Outcome isa} (h : Phase x o c M t mem) (hs : stepOne Arch.armv8 t tid mem = some outs)
    (ho : .ok oc ∈ outs) (hp0 : t.prom ≠ []) :
    (oc.mem = mem ∧ Phase x o c M oc.thread oc.mem) ∨ Win x o c (mem.last + 1) oc.thread oc.mem := by
  have hsinv := (step_sinv h.sinv hs ho).1
  obtain ⟨hS, i, hi, hpc⟩ := h.sinv
  obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil _ hp0
  have hql : q < mem.last + 1 := Nat.lt_succ_of_le (h.wf q hq)
  -- a taken ticket is at positions 6–13
  have notk : ¬ i ∈ tkHeld → ¬ (Ticketed t ∧ tk t = M) := fun hn h1 => hn ((ticketed_iff hi hpc).mp h1.1)
  -- the facts of a step between two positions keeping `X3`
  have keep : ∀ j ∈ tkLoopPcs, oc.thread.st.st.2 = pcA j → oc.thread.st.st.1.regs.X3 = t.st.st.1.regs.X3 →
      (i ∈ tkHeld → j ∈ tkHeld) → Ticketed t ∧ tk t = M → Ticketed oc.thread ∧ tk oc.thread = M := by
    intro j hj hpc' h3 hij ⟨h1, h2⟩
    have hi1 := (ticketed_iff hi hpc).mp h1
    have e := same_tk hi hj hpc hpc' h3 (iff_of_true hi1 (hij hi1))
    exact ⟨e.1.mpr h1, (e.2 h1).trans h2⟩
  have hi' := hi
  simp only [tkLoopPcs, List.mem_cons, List.not_mem_nil, or_false] at hi'
  rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨hm, -, hpr, -⟩ := s1 hS hs ho hpc
    exact .inl ⟨hm, phase_quiet h hs ho hm hpr fun h1 => absurd h1 (notk (by decide))⟩
  · obtain ⟨hm, -, hpr, -⟩ := s3 hS hs ho hpc
    exact .inl ⟨hm, phase_quiet h hs ho hm hpr fun h1 => absurd h1 (notk (by decide))⟩
  · -- 4: `LDADDA`
    obtain ⟨tr, old, hst, -, -, hw⟩ := SpinSemShape.spec_rmwo_p _ _ rfl
      (exec_ldadda _ (hS.at (by decide) (by decide) hpc) hS.x0 hS.dx) hs ho
    -- the holder has reserved `M`
    obtain ⟨tsM, htsM, wM, hwM, hlM, hvM⟩ : ∃ ts ∈ t.prom, ∃ w, mem.get? ts = some w ∧ w.loc = L4 x ∧
        w.val.toNat = M + 1 := h.hold.resolve_left (notk (by decide))
    have hMl : tsM ≤ mem.last := mem.last_le_of_get?_eq_some hwM
    rcases hw with ⟨h1, -⟩ | ⟨new, hnew, ⟨hm, hpr, -, -, hcoh, -⟩ | ⟨ts, hts, hg, -, hm, hpr, -, -, -, -⟩⟩
    · exact absurd h1 (by simp)
    · -- fresh: the `next` promise is below `coh next`
      right
      have hlast : oc.mem.last = mem.last + 1 := by rw [hm, Memory.last_append]
      have hin : tsM ∈ oc.thread.prom := by
        rw [hpr]; exact (List.mem_erase_of_ne (by omega_t)).mpr (List.mem_append_left _ htsM)
      refine ⟨hsinv, by omega_t, tsM, hin, by omega_t, .inl ⟨hin, .inr ⟨wM, ?_, ?_⟩⟩⟩
      · rw [hm]; rw [(Memory.Prefix.append _ _).get? hMl]; exact hwM
      · rw [hlM]; exact Nat.le_trans (by omega_t : tsM ≤ mem.last + 1) hcoh
    · -- fulfilment
      left
      refine ⟨hm, ?_⟩
      by_cases hin : tsM ∈ oc.thread.prom
      · obtain ⟨-, -, hf', -, -, hp'⟩ := stepOne_silent_nt Arch.armv8 hs ho h.fwd
        exact ⟨hsinv, step_reginv h.sinv h.reg hs ho, hf', hp' h.wf, hm ▸ h.hno,
          .inr ⟨tsM, hin, wM, hm ▸ hwM, hlM, hvM⟩⟩
      · -- the `next := M + 1` promise fulfilled: ticket `M` taken
        have e : tsM = ts := Classical.byContradiction fun hne =>
          hin (by rw [hpr]; exact (List.mem_erase_of_ne hne).mpr htsM)
        subst e
        rw [hg] at hwM
        cases hwM
        cases Option.some.inj hnew
        have h6 := h.reg.x6' hi hpc (by decide)
        have hval : (BitVec.setWidth 128 (BitVec.setWidth 32 old + BitVec.setWidth 32 t.st.st.1.regs.X6.toBitVec)).toNat =
            (old.toNat % 2 ^ 32 + 1) % 2 ^ 32 := by
          simp only [wn] at h6
          simp only [BitVec.toNat_setWidth, BitVec.toNat_add]
          have : t.st.st.1.regs.X6.toBitVec.toNat % 2 ^ 32 = 1 := h6
          rw [this]; omega
        have hk : tk oc.thread = old.toNat % 2 ^ 32 := by
          unfold tk; rw [hst]; exact wn_setWidth' old
        have hpc' : oc.thread.st.st.2 = pcA 6 := by rw [hst] <;> rfl
        obtain ⟨-, -, hf', -, -, hp'⟩ := stepOne_silent_nt Arch.armv8 hs ho h.fwd
        refine ⟨hsinv, step_reginv h.sinv h.reg hs ho, hf', hp' h.wf, hm ▸ h.hno,
          .inl ⟨(ticketed_iff (by decide) hpc').mpr (by decide), ?_⟩⟩
        rw [hk]
        have := hval.symm.trans hvM
        omega
  · obtain ⟨ts, v, hst, -, -, hm, hpr, -⟩ := s6 hS hs ho hpc
    exact .inl ⟨hm, phase_quiet h hs ho hm hpr (keep 7 (by decide) (by rw [hst] <;> rfl) (by rw [hst] <;> rfl)
      (fun _ => by decide))⟩
  · obtain ⟨sf, hst, -, hm, hpr, -⟩ := s7 hS hs ho hpc
    exact .inl ⟨hm, phase_quiet h hs ho hm hpr (keep 8 (by decide) (by rw [hst] <;> rfl) (by rw [hst] <;> rfl)
      (fun _ => by decide))⟩
  · obtain ⟨hm, hst, hpr, -⟩ := s8 hS hs ho hpc
    by_cases hz : t.st.st.1.status.z = true
    · rw [ite_eq_left hz] at hst
      exact .inl ⟨hm, phase_quiet h hs ho hm hpr (keep 9 (by decide) (by rw [hst] <;> rfl) (by rw [hst] <;> rfl)
        (fun _ => by decide))⟩
    · rw [ite_eq_right hz] at hst
      exact .inl ⟨hm, phase_quiet h hs ho hm hpr (keep 6 (by decide) (by rw [hst] <;> rfl) (by rw [hst] <;> rfl)
        (fun _ => by decide))⟩
  · obtain ⟨v, hst, hm, hpr, -⟩ := s9 hS hs ho hpc
    exact .inl ⟨hm, phase_quiet h hs ho hm hpr (keep 10 (by decide) (by rw [hst] <;> rfl) (by rw [hst] <;> rfl)
      (fun _ => by decide))⟩
  · obtain ⟨hm, hst, hpr, -⟩ := s10 hS hs ho hpc
    exact .inl ⟨hm, phase_quiet h hs ho hm hpr (keep 11 (by decide) (by rw [hst] <;> rfl) (by rw [hst] <;> rfl)
      (fun _ => by decide))⟩
  · -- 11: `STR` counter
    obtain ⟨hst, hw⟩ := spec_store_p _ _ (exec_str_c _ (hS.at (by decide) (by decide) hpc) hS.x2 hS.dc) hs ho
    have hpc' : oc.thread.st.st.2 = pcA 12 := by rw [hst] <;> rfl
    rcases hw with ⟨hm, hpr, hvw⟩ | ⟨ts, -, hg, -, -, hm, hpr, -⟩
    · -- fresh: `vwOld` past every promise, before the `STLR`
      right
      have hlast : oc.mem.last = mem.last + 1 := by rw [hm, Memory.last_append]
      have hpr' : oc.thread.prom = t.prom := hpr.trans (erase_fresh h.wf)
      exact ⟨hsinv, by omega_t, q, hpr' ▸ hq, hql, .inr (.inl ⟨.inl hpc', hvw rfl⟩)⟩
    · left
      obtain ⟨-, -, hf', -, -, hp'⟩ := stepOne_silent_nt Arch.armv8 hs ho h.fwd
      refine ⟨hm, hsinv, step_reginv h.sinv h.reg hs ho, hf', hp' h.wf, hm ▸ h.hno, ?_⟩
      rcases h.hold with h1 | ⟨tsM, htsM, wM, hwM, hlM, hvM⟩
      · exact .inl (keep 12 (by decide) hpc' (by rw [hst]) (fun _ => by decide) h1)
      · have hne : tsM ≠ ts := fun e => by
          subst e; rw [hg] at hwM; cases hwM; exact hxc hlM.symm
        exact .inr ⟨tsM, by rw [hpr]; exact (List.mem_erase_of_ne hne).mpr htsM, wM, hm ▸ hwM, hlM, hvM⟩
  · obtain ⟨hm, hst, hpr, -⟩ := s12 hS hs ho hpc
    exact .inl ⟨hm, phase_quiet h hs ho hm hpr (keep 13 (by decide) (by rw [hst] <;> rfl) (by rw [hst] <;> rfl)
      (fun _ => by decide))⟩
  · -- 13: `STLR`
    obtain ⟨hst, hw⟩ := spec_store_rel _ _ rfl (exec_stlr _ (hS.at (by decide) (by decide) hpc) hS.x1 hS.dO) hs ho
    have hpc' : oc.thread.st.st.2 = pcA 14 := by rw [hst] <;> rfl
    rcases hw with ⟨hm, hpr, hvr⟩ | ⟨ts, -, hg, -, hm, hpr, -⟩
    · -- fresh: `vRel` past every promise, before the `LDADDA`
      right
      have hlast : oc.mem.last = mem.last + 1 := by rw [hm, Memory.last_append]
      have hpr' : oc.thread.prom = t.prom := hpr.trans (erase_fresh h.wf)
      exact ⟨hsinv, by omega_t, q, hpr' ▸ hq, hql, .inr (.inr ⟨.inl hpc', hvr⟩)⟩
    · left
      obtain ⟨-, -, hf', -, -, hp'⟩ := stepOne_silent_nt Arch.armv8 hs ho h.fwd
      refine ⟨hm, hsinv, step_reginv h.sinv h.reg hs ho, hf', hp' h.wf, hm ▸ h.hno, ?_⟩
      rcases h.hold with ⟨-, h2⟩ | ⟨tsM, htsM, wM, hwM, hlM, hvM⟩
      · -- the holder of `M` writes `owner := M + 1`: no such message to fulfil
        exfalso
        have h4 := h.reg.x4 hpc
        refine h.hno ts _ hg rfl ?_
        show (BitVec.setWidth 128 (BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec)).toNat = M + 1
        rw [val_setWidth', h4]
        unfold tk at h2
        rw [h2]; exact Nat.mod_eq_of_lt hM32
      · have hne : tsM ≠ ts := fun e => by
          subst e; rw [hg] at hwM; cases hwM; exact hxo hlM.symm
        exact .inr ⟨tsM, by rw [hpr]; exact (List.mem_erase_of_ne hne).mpr htsM, wM, hm ▸ hwM, hlM, hvM⟩
  · obtain ⟨hm, -, hpr, -⟩ := s14 hS hs ho hpc
    exact .inl ⟨hm, phase_quiet h hs ho hm hpr fun h1 => absurd h1 (notk (by decide))⟩
  · obtain ⟨hm, -, hpr, -⟩ := s15 hS hs ho hpc
    exact .inl ⟨hm, phase_quiet h hs ho hm hpr fun h1 => absurd h1 (notk (by decide))⟩
  · rw [stepOne_end hS hpc] at hs; cases hs

/-- **Every certification of the holder, cut at its first empty promise set,
has no fresh write.** -/
theorem phase_run {tid : Nat} : ∀ {n : Nat} {p q : Thread isa × Memory}, ThreadNPn Arch.armv8 tid n p q →
    q.1.prom = [] → Phase x o c M p.1 p.2 → ∃ t', ThreadNPn Arch.armv8 tid n p (t', p.2) ∧ t'.prom = [] := by
  intro n p q h
  induction h with
  | refl n p => intro hq _; exact ⟨p.1, .refl _ _, hq⟩
  | @step n p q r hs h ih =>
    intro hq hP
    by_cases hp0 : p.1.prom = []
    · exact ⟨p.1, .refl _ _, hp0⟩
    obtain ⟨outs, oc, hs', ho, rfl⟩ := hs
    rcases phase_step hxo hxc hM32 hP hs' ho hp0 with ⟨hm, hP'⟩ | hW
    · obtain ⟨t', h', ht'⟩ := ih hq hP'
      refine ⟨t', .step ⟨outs, oc, hs', ho, rfl⟩ ?_, ht'⟩
      rw [← hm]; exact h'
    · exact absurd hq (win_run h hW)

end PhaseStep

/-! ## F3 -/

/-- `H` holds ticket `M`: taken (positions 6–13, low word of `X3` is `M`), or
reserved (an outstanding promise of value `M + 1` to `next`). -/
def HoldsLoop (x : BitVec 64) (u : Thread isa) (mem : Memory) (M : Nat) : Prop :=
  (TicketLoopInv.Ticketed u ∧ TicketLoopInv.tk u = M) ∨
  (¬ TicketLoopInv.Ticketed u ∧
    ∃ ts ∈ u.prom, ∃ w, mem.get? ts = some w ∧ w.loc = L4 x ∧ w.val.toNat = M + 1)

/-- **F3: the holder of ticket `M` certifies without fresh writes** (semantic
machine). On a semantic trace from a start configuration, a certifiable thread
holding `M`, with no `owner := M + 1` message in memory, has no promise or a
certification that writes nothing fresh (`NACertG`).

`hM32` (`M + 1 < 2 ^ 32`, the owner counter not wrapping at `2 ^ 32 - 1`) is a
hypothesis here; `TicketLoopInvP.holder_nacert'` is the `hM32`-free form, which
derives it from the trace invariant. `_hM` is unused (kept so the statement is
unchanged). -/
theorem holder_nacert {fuel k N : Nat}
    {x o c : BitVec 64} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : TkLoopStart k N x o c states initMem) (tr : TraceSem Arch.armv8 fuel isa)
    (h0 : tr.cfg 0 = Config.init states initMem) (i : Nat) {H M : Nat} {u : Thread isa}
    (hu : (tr.cfg i).threads[H]? = some u)
    (_hM : ((tr.cfg i).mem.finalVal (L4 o)).toNat = M)
    (hh : HoldsLoop x u (tr.cfg i).mem M)
    (hno : ∀ ts w, (tr.cfg i).mem.get? ts = some w → w.loc = L4 o → w.val.toNat ≠ M + 1)
    (hc : CertOkN Arch.armv8 H u (tr.cfg i).mem fuel) (hM32 : M + 1 < 2 ^ 32) :
    u.prom = [] ∨ NACertG Arch.armv8 fuel H u (tr.cfg i).mem := by
  by_cases hp0 : u.prom = []
  · exact .inl hp0
  right
  obtain ⟨hf, hwf⟩ := trace_wf tr h0 i H u hu
  have hP : Phase x o c M u (tr.cfg i).mem :=
    ⟨trace_sinv hs tr h0 i H u hu, trace_reginv hs tr h0 i H u hu, hf, hwf, hno,
      hh.imp id fun h => h.2⟩
  obtain ⟨t', m', hr, hq⟩ := hc
  exact phase_run (SpinStep.loc_ne hs.hxo) (SpinStep.loc_ne hs.hxc) hM32 hr hq hP

end Kraken.Promising.Live.TicketLoopHolder
