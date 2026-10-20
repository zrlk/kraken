/-
**Solo runs of the repeated-acquire ticket-lock worker
with outstanding promises** (`tkLoopWorker`, semantic machine).

A worker's own steps keep a per-thread invariant `TI` that holds for any
promise set (no global hypothesis): `SInv`, `RegInv`, the round counter facts,
the `owner` value it read (`ORdP`: a readable `owner` message that is not one
of its own promises), its `next` message when it holds a ticket (`txn`: not
an outstanding promise), and `PCov`: every message of the thread above its
`coh` of the message's location is one of its outstanding promises.

`step_ti`: one instruction step keeps `TI` and is described by `Eff` (quiet,
`LDADDA`, `STR`, `STLR`; each a fresh append or the fulfilment of an
outstanding promise).

The certification analysis (`cert_x`, `cert_o`, `cert_cnt`): a worker that
empties its promise set alone

- fulfils a `next` promise `p` with an atomic read of the last `next`
  message below `p` (the messages between are its own, above its `coh`, hence
  promises, which the fulfilment of `p` would kill);
- fulfils an `owner` promise `p` without a fresh write before it (any fresh
  write raises `vwOld` past `p`, and the release `STLR` fulfils only above
  `vwOld`), at a ticket `kk` read from a readable `owner` message below `p`
  and taken with a `next` message below `p`; no own `owner` message below `p`
  has the value `kk + 1` (it would be an outstanding promise by `OH`, killed
  by the fulfilment of `p`);
- has at most as many `next` promises as `LDADDA`s left (`phi`).
-/
import Kraken.Promising.LiveTicketLoopHolder

namespace Kraken.Promising.Live.TicketLoopCert

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live Kraken.Promising.Live.Sem
open Kraken.Promising.Live.TicketLoop Kraken.Promising.Live.TicketLoopTrees Kraken.Promising.Live.TicketLoopStatic
open Kraken.Promising.Live.TicketLoopInv Kraken.Promising.Live.TicketLoopHolder
open Kraken.Promising.Live.TicketStep Kraken.Promising.Live.SemShape Kraken.Promising.Live.LoopFacts
open Kraken.Promising.Live.TicketInv (wn L4 w32_eq_iff)
open Kraken.Promising.Live.TicketTrees (w32)
open Kraken.Promising.SLR.A64Trees (goto)

set_option linter.unusedSectionVars false

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

/-! ## Instruction-level facts with any promise set -/

section Spec

variable {I : ISA} (A : Arch) (tid : Nat) {t : Thread I} {mem : Memory} {outs : List (Except String (Outcome I))}
  {o : Outcome I}

theorem writeIn_mono {m : Memory} {l : Loc} {lo hi hi' : Time} (h : m.writeIn l lo hi = false) (hh : hi' ≤ hi) :
    m.writeIn l lo hi' = false :=
  SpinSemSwpSolo.writeIn_le h hh

/-- **An always-writing RMW, with any promise set**, with the read's
write-free window up to the coherence view and the views after it. -/
theorem spec_rmw_w (hA : A.rmwFence = false) {k : RmwKind} {l : Loc} {g : Val → Val} {f : Val → I.State}
    (hk : (A.storeKind (A.rmwKind k).storeKind == .nt) = false)
    (hex : I.exec t.st = some (.rmw k false l (fun old => some (g old)) fun v => .done (f v)))
    (hs : stepOne A t tid mem = some outs) (ho : .ok o ∈ outs) :
    ∃ tr old, o.thread.st = f old ∧ mem.read? l tr = some old ∧ mem.writeIn l tr (t.views.getCoh l) = false ∧
      ((o.mem = (mem.append { loc := l, val := g old, tid }).1 ∧
        o.thread.prom = (t.prom ++ [mem.last + 1]).erase (mem.last + 1) ∧
        mem.last + 1 ≤ o.thread.views.vwOld ∧ t.views.vwOld ≤ o.thread.views.vwOld ∧
        mem.last + 1 ≤ o.thread.views.getCoh l ∧ mem.atomic l tid tr (mem.last + 1) = true) ∨
       (∃ ts ∈ t.prom, mem.get? ts = some { loc := l, val := g old, tid } ∧ t.views.getCoh l < ts ∧
        o.mem = mem ∧ o.thread.prom = t.prom.erase ts ∧ t.views.vwOld ≤ o.thread.views.vwOld ∧
        ts ≤ o.thread.views.getCoh l ∧ tr < ts ∧ mem.atomic l tid tr ts = true)) := by
  obtain ⟨tr, old, hst, hrd, -, hw, hcase⟩ := SpinSemShape.spec_rmwo_pw A tid hA hex hs ho
  rcases hcase with ⟨h1, -⟩ | ⟨new, h1, ⟨e1, e2, e3, e4, e5, e6⟩ | h⟩
  · simp at h1
  · cases Option.some.inj h1; exact ⟨tr, old, hst, hrd, hw, .inl ⟨e1, e2, e3 hk, e4, e5, e6⟩⟩
  · cases Option.some.inj h1; exact ⟨tr, old, hst, hrd, hw, .inr h⟩

end Spec

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout tkLoopWorker)]

set_option hygiene false in
local notation "pcA" => (layout tkLoopWorker).addrOf

/-! ## The solo-run predicates -/

/-- A message of `tid` to `next` with value `v`. -/
def XMsg (x : BitVec 64) (tid : Nat) (mem : Memory) (ts : Time) (v : Nat) : Prop :=
  ∃ w, mem.get? ts = some w ∧ w.loc = L4 x ∧ w.tid = tid ∧ w.val.toNat = v

/-- A readable `owner` value (low word `k`), at a timestamp that is not one of
the thread's outstanding promises. -/
def ORdP (o : BitVec 64) (t : Thread isa) (mem : Memory) (k : Nat) : Prop :=
  ∃ tr v, mem.read? (L4 o) tr = some v ∧ v.toNat % 2 ^ 32 = k ∧ tr ∉ t.prom

/-- **Every message of `tid` above its `coh` of the message's location is an
outstanding promise.** -/
def PCov (tid : Nat) (t : Thread isa) (mem : Memory) : Prop :=
  ∀ ts w, mem.get? ts = some w → w.tid = tid → t.views.getCoh w.loc < ts → ts ∈ t.prom

/-- Thread `tid` holds ticket `v`: taken, or reserved by an outstanding
promise of its `next` message of value `v + 1` (low word). -/
def HoldsV (x : BitVec 64) (tid : Nat) (t : Thread isa) (mem : Memory) (v : Nat) : Prop :=
  (Ticketed t ∧ tk t = v) ∨ ∃ ts ∈ t.prom, XMsg x tid mem ts ((v + 1) % 2 ^ 32)

/-- **An `owner` message of a thread that still holds its ticket is an
outstanding promise.** -/
def OH (x o : BitVec 64) (tid : Nat) (t : Thread isa) (mem : Memory) : Prop :=
  ∀ ts w, mem.get? ts = some w → w.loc = L4 o → w.tid = tid → ∀ v, w.val.toNat = (v + 1) % 2 ^ 32 →
    HoldsV x tid t mem v → ts ∈ t.prom

/-- Position-dependent counts: `1` at the positions `L`. -/
noncomputable def pv (L : List Nat) (t : Thread isa) : Nat :=
  open Classical in if ∃ i ∈ L, t.st.st.2 = pcA i then 1 else 0

/-- The writes the worker has done in its run of `k` rounds: three per
completed round, and one, two or three in the current round past its
`LDADDA`, `STR`, `STLR`. -/
noncomputable def wr (k : Nat) (t : Thread isa) : Nat :=
  3 * (k - wn t.st.st.1.regs.X7) + pv tkBusy t + pv [12, 13, 14] t + pv [14] t

/-- The `LDADDA`s the worker has left: `X7`, less one in a round past its
`LDADDA`. -/
noncomputable def phi (t : Thread isa) : Nat := wn t.st.st.1.regs.X7 - pv tkBusy t

theorem pv_at {L : List Nat} (hL : ∀ j ∈ L, j ∈ tkLoopPcs) {t : Thread isa} {i : Nat} (hi : i ∈ tkLoopPcs)
    (hpc : t.st.st.2 = pcA i) : pv L t = if i ∈ L then 1 else 0 := by
  unfold pv
  by_cases h : i ∈ L
  · rw [ite_eq_left ⟨i, h, hpc⟩, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right]
    rintro ⟨j, hj, e⟩
    exact h (by rwa [addrOf_inj hi (hL j hj) (hpc.symm.trans e)])

/-- The counts at a position. -/
theorem cnt_at (k : Nat) {t : Thread isa} {i : Nat} (hi : i ∈ tkLoopPcs) (hpc : t.st.st.2 = pcA i) :
    taken k t = k - wn t.st.st.1.regs.X7 + (if i ∈ tkBusy then 1 else 0) ∧
    wr k t = 3 * (k - wn t.st.st.1.regs.X7) + (if i ∈ tkBusy then 1 else 0) + (if i ∈ [12, 13, 14] then 1 else 0) +
      (if i ∈ [14] then 1 else 0) ∧
    phi t = wn t.st.st.1.regs.X7 - (if i ∈ tkBusy then 1 else 0) := by
  refine ⟨taken_at hi hpc, ?_, ?_⟩
  · unfold wr
    rw [pv_at busy_sub hi hpc, pv_at (by decide) hi hpc, pv_at (by decide) hi hpc]
  · unfold phi; rw [pv_at busy_sub hi hpc]

/-- **The per-thread invariant of a worker, for any promise set.** -/
structure TI (k : Nat) (x o c : BitVec 64) (tid : Nat) (t : Thread isa) (mem : Memory) : Prop where
  sinv : SInv x o c t.st
  reg : RegInv t.st
  k7 : wn t.st.st.1.regs.X7 ≤ k
  x7 : ∀ i ∈ [4, 6, 7, 8, 9, 10, 11, 12, 13, 14], t.st.st.2 = pcA i → wn t.st.st.1.regs.X7 ≠ 0
  e7 : t.st.st.2 = pcA 17 → wn t.st.st.1.regs.X7 = 0
  f7 : t.st.st.2 = pcA 7 → ORdP o t mem (wn t.st.st.1.regs.X4)
  f8 : t.st.st.2 = pcA 8 → t.st.st.1.status.z = true → ORdP o t mem (wn t.st.st.1.regs.X3)
  f9 : ∀ i ∈ [9, 10, 11, 12, 13], t.st.st.2 = pcA i → ORdP o t mem (wn t.st.st.1.regs.X3)
  txn : Ticketed t → ∃ ts, ts ∉ t.prom ∧ XMsg x tid mem ts ((tk t + 1) % 2 ^ 32)
  pcov : PCov tid t mem
  fwd : t.views.FwdOk
  wf : ∀ p ∈ t.prom, p ≤ mem.last
  nd : t.prom.Nodup

/-! ## Larger memories and own promises -/

theorem read?_le {mem : Memory} {l : Loc} {tr : Time} {v : Val} (h : mem.read? l tr = some v) : tr ≤ mem.last := by
  rcases mem.read?_eq_some h with ⟨rfl, -⟩ | ⟨w, hw, -, -⟩
  · exact Nat.zero_le _
  · exact mem.last_le_of_get?_eq_some hw

theorem ORdP.mono {o : BitVec 64} {t t' : Thread isa} {mem mem' : Memory} {k : Nat} (h : ORdP o t mem k)
    (hp : mem.Prefix mem') (hpr : ∀ ts ∈ t'.prom, ts ∈ t.prom ∨ mem.last < ts) : ORdP o t' mem' k := by
  obtain ⟨tr, v, hr, hv, hn⟩ := h
  refine ⟨tr, v, by rw [hp.read? (read?_le hr)]; exact hr, hv, fun hin => ?_⟩
  rcases hpr tr hin with h | h
  · exact hn h
  · have := read?_le hr; omega_t

theorem XMsg.mono {x : BitVec 64} {tid : Nat} {mem mem' : Memory} {ts : Time} {v : Nat} (h : XMsg x tid mem ts v)
    (hp : mem.Prefix mem') : XMsg x tid mem' ts v := by
  obtain ⟨w, hw, h1⟩ := h
  exact ⟨w, by rw [hp.get? (mem.last_le_of_get?_eq_some hw)]; exact hw, h1⟩

theorem XMsg.le {x : BitVec 64} {tid : Nat} {mem : Memory} {ts : Time} {v : Nat} (h : XMsg x tid mem ts v) :
    ts ≤ mem.last :=
  let ⟨_, hw, _⟩ := h; mem.last_le_of_get?_eq_some hw

/-- **`TI` against a larger memory** whose new messages are not the thread's. -/
theorem TI.mono {k : Nat} {x o c : BitVec 64} {tid : Nat} {t : Thread isa} {mem mem' : Memory}
    (h : TI k x o c tid t mem) (hp : mem.Prefix mem')
    (hnew : ∀ ts w, mem'.get? ts = some w → mem.last < ts → w.tid ≠ tid) : TI k x o c tid t mem' := by
  have hpr : ∀ ts ∈ t.prom, ts ∈ t.prom ∨ mem.last < ts := fun _ h => .inl h
  refine ⟨h.sinv, h.reg, h.k7, h.x7, h.e7, fun a => (h.f7 a).mono hp hpr, fun a b => (h.f8 a b).mono hp hpr,
    fun i hi a => (h.f9 i hi a).mono hp hpr, fun a => ?_, fun ts w hw hid hc => ?_, h.fwd,
    fun p hp' => Nat.le_trans (h.wf p hp') hp.last_le, h.nd⟩
  · obtain ⟨ts, hn, hx⟩ := h.txn a; exact ⟨ts, hn, hx.mono hp⟩
  · by_cases hl : ts ≤ mem.last
    · rw [hp.get? hl] at hw; exact h.pcov ts w hw hid hc
    · exact absurd hid (hnew ts w hw (by omega_t))

/-- **`TI` after an own promise step.** -/
theorem TI.prom {k : Nat} {x o c : BitVec 64} {tid : Nat} {t : Thread isa} {mem : Memory}
    (h : TI k x o c tid t mem) (w : Msg) : TI k x o c tid (promThread t mem w) (mem.append w).1 := by
  have hp := Memory.Prefix.append mem w
  have hpr : ∀ ts ∈ (promThread t mem w).prom, ts ∈ t.prom ∨ mem.last < ts := fun ts h' => by
    rcases List.mem_append.mp h' with h' | h'
    · exact .inl h'
    · simp only [List.mem_singleton, Memory.append_time] at h'; right; omega_t
  refine ⟨h.sinv, h.reg, h.k7, h.x7, h.e7, fun a => (h.f7 a).mono hp hpr, fun a b => (h.f8 a b).mono hp hpr,
    fun i hi a => (h.f9 i hi a).mono hp hpr, fun a => ?_, fun ts w' hw hid hc => ?_, h.fwd, fun p hp' => ?_, ?_⟩
  · obtain ⟨ts, hn, hx⟩ := h.txn a
    refine ⟨ts, fun hin => ?_, hx.mono hp⟩
    rcases hpr ts hin with h1 | h1
    · exact hn h1
    · have := hx.le; omega_t
  · rcases mem.get?_append_eq_some w hw with ⟨hl, hw'⟩ | ⟨e, -⟩
    · exact List.mem_append_left _ (h.pcov ts w' hw' hid hc)
    · exact List.mem_append_right _ (by rw [e]; simp [Memory.append_time])
  · rcases List.mem_append.mp hp' with h' | h'
    · exact Nat.le_trans (h.wf p h') hp.last_le
    · simp only [List.mem_singleton, Memory.append_time] at h'; rw [h', Memory.last_append]; exact Nat.le_refl _
  · refine List.nodup_append.mpr ⟨h.nd, by simp, fun a ha b hb e => ?_⟩
    simp only [List.mem_singleton, Memory.append_time] at hb
    have := h.wf a ha
    omega_t

/-! ## One step -/

theorem pcov_quiet {tid : Nat} {t t' : Thread isa} {mem : Memory} (h : PCov tid t mem)
    (hp : t'.prom = t.prom) (hc : ∀ l, t.views.getCoh l ≤ t'.views.getCoh l) : PCov tid t' mem :=
  fun ts w hw hid hlt => hp ▸ h ts w hw hid (Nat.lt_of_le_of_lt (hc _) hlt)

theorem pcov_ful {tid : Nat} {t t' : Thread isa} {mem : Memory} (h : PCov tid t mem) {ts0 : Time} {w0 : Msg}
    (hg : mem.get? ts0 = some w0) (hp : t'.prom = t.prom.erase ts0) (hc : ∀ l, t.views.getCoh l ≤ t'.views.getCoh l)
    (hc0 : ts0 ≤ t'.views.getCoh w0.loc) : PCov tid t' mem := by
  intro ts w hw hid hlt
  have h1 := h ts w hw hid (Nat.lt_of_le_of_lt (hc _) hlt)
  rw [hp]
  refine (List.mem_erase_of_ne fun e => ?_).mpr h1
  subst e; rw [hg] at hw; cases hw; omega_t

theorem pcov_fresh {tid : Nat} {t t' : Thread isa} {mem : Memory} (h : PCov tid t mem) {w0 : Msg}
    (hp : t'.prom = t.prom) (hc : ∀ l, t.views.getCoh l ≤ t'.views.getCoh l)
    (hc0 : mem.last + 1 ≤ t'.views.getCoh w0.loc) : PCov tid t' (mem.append w0).1 := by
  intro ts w hw hid hlt
  rcases mem.get?_append_eq_some w0 hw with ⟨-, hw'⟩ | ⟨e, rfl⟩
  · rw [hp]; exact h ts w hw' hid (Nat.lt_of_le_of_lt (hc _) hlt)
  · omega_t

/-- `TI` at a known position `j` from the facts that position needs. -/
theorem ti_of {k : Nat} {x o c : BitVec 64} {tid : Nat} {t : Thread isa} {mem : Memory} {j : Nat}
    (hj : j ∈ tkLoopPcs) (hpc : t.st.st.2 = pcA j) (hS : SInv x o c t.st) (hR : RegInv t.st)
    (hk7 : wn t.st.st.1.regs.X7 ≤ k)
    (hx7 : j ∈ [4, 6, 7, 8, 9, 10, 11, 12, 13, 14] → wn t.st.st.1.regs.X7 ≠ 0)
    (he7 : j = 17 → wn t.st.st.1.regs.X7 = 0)
    (hf7 : j = 7 → ORdP o t mem (wn t.st.st.1.regs.X4))
    (hf8 : j = 8 → t.st.st.1.status.z = true → ORdP o t mem (wn t.st.st.1.regs.X3))
    (hf9 : j ∈ [9, 10, 11, 12, 13] → ORdP o t mem (wn t.st.st.1.regs.X3))
    (htx : j ∈ tkHeld → ∃ ts, ts ∉ t.prom ∧ XMsg x tid mem ts ((tk t + 1) % 2 ^ 32))
    (hpcov : PCov tid t mem) (hfwd : t.views.FwdOk) (hwf : ∀ p ∈ t.prom, p ≤ mem.last) (hnd : t.prom.Nodup) :
    TI k x o c tid t mem := by
  have e : ∀ {i}, i ∈ tkLoopPcs → t.st.st.2 = pcA i → i = j := fun hi h => addrOf_inj hi hj (h.symm.trans hpc)
  refine ⟨hS, hR, hk7, fun i hi h => ?_, fun h => he7 (e (by decide) h).symm, fun h => hf7 (e (by decide) h).symm,
    fun h => hf8 (e (by decide) h).symm, fun i hi h => ?_, fun ht => htx ((ticketed_iff hj hpc).mp ht), hpcov, hfwd,
    hwf, hnd⟩
  · have := e ((by decide : ∀ i ∈ [4, 6, 7, 8, 9, 10, 11, 12, 13, 14], i ∈ tkLoopPcs) i hi) h
    subst this; exact hx7 hi
  · have := e ((by decide : ∀ i ∈ [9, 10, 11, 12, 13], i ∈ tkLoopPcs) i hi) h
    subst this; exact hf9 hi

/-- The counts across a step that keeps `X7` (positions in the same class). -/
theorem quiet_cnt (k : Nat) {t t' : Thread isa} {i j d : Nat} (hi : i ∈ tkLoopPcs) (hj : j ∈ tkLoopPcs)
    (hpc : t.st.st.2 = pcA i) (hpc' : t'.st.st.2 = pcA j) (h7 : t'.st.st.1.regs.X7 = t.st.st.1.regs.X7)
    (hb : (if i ∈ tkBusy then 1 else 0) = (if j ∈ tkBusy then 1 else 0))
    (hw : (if i ∈ [12, 13, 14] then 1 else 0) + (if i ∈ [14] then 1 else 0) + d =
      (if j ∈ [12, 13, 14] then 1 else 0) + (if j ∈ [14] then 1 else 0)) :
    taken k t' = taken k t ∧ wr k t' = wr k t + d ∧ phi t' = phi t := by
  obtain ⟨a1, a2, a3⟩ := cnt_at k hi hpc
  obtain ⟨b1, b2, b3⟩ := cnt_at k hj hpc'
  rw [h7] at b1 b2 b3
  omega

theorem ORdP.keep {o : BitVec 64} {t t' : Thread isa} {mem mem' : Memory} {k k' : Nat} (h : ORdP o t mem k)
    (hp : mem.Prefix mem') (hpr : ∀ ts ∈ t'.prom, ts ∈ t.prom ∨ mem.last < ts) (e : k = k') : ORdP o t' mem' k' :=
  e ▸ h.mono hp hpr

theorem txn_keep {x : BitVec 64} {tid : Nat} {t t' : Thread isa} {mem mem' : Memory}
    (htx : Ticketed t → ∃ ts, ts ∉ t.prom ∧ XMsg x tid mem ts ((tk t + 1) % 2 ^ 32)) (ht : Ticketed t)
    (hk : tk t' = tk t) (hp : mem.Prefix mem') (hpr : ∀ ts ∈ t'.prom, ts ∈ t.prom ∨ mem.last < ts) :
    ∃ ts, ts ∉ t'.prom ∧ XMsg x tid mem' ts ((tk t' + 1) % 2 ^ 32) := by
  obtain ⟨ts, hn, hx⟩ := htx ht
  refine ⟨ts, fun hin => ?_, hk ▸ hx.mono hp⟩
  rcases hpr ts hin with h1 | h1
  · exact hn h1
  · have := hx.le; omega_t

theorem pr_eq {t t' : Thread isa} {mem : Memory} (h : t'.prom = t.prom) : ∀ ts ∈ t'.prom, ts ∈ t.prom ∨ mem.last < ts :=
  fun _ h' => .inl (h ▸ h')

theorem pr_erase {t t' : Thread isa} {mem : Memory} {a : Time} (h : t'.prom = t.prom.erase a) :
    ∀ ts ∈ t'.prom, ts ∈ t.prom ∨ mem.last < ts :=
  fun _ h' => .inl (List.mem_of_mem_erase (h ▸ h'))

/-- **What one instruction step of the worker does**: nothing to memory or
promises (`quiet`), or its `LDADDA` (`ld`), `STR` (`st`) or `STLR` (`rl`),
each a fresh append or the fulfilment of an outstanding promise. -/
inductive Eff (k : Nat) (x o c : BitVec 64) (tid : Nat) (t : Thread isa) (mem : Memory) (oc : Outcome isa) :
    Prop
  | quiet (hm : oc.mem = mem) (hp : oc.thread.prom = t.prom) (htk : Ticketed oc.thread ↔ Ticketed t)
      (hk : Ticketed t → tk oc.thread = tk t) (hn : taken k oc.thread = taken k t) (hw : wr k oc.thread = wr k t)
      (hphi : phi oc.thread = phi t) (hv : t.views.vwOld ≤ oc.thread.views.vwOld)
  | ld (tr : Time) (old v : Val) (hrd : mem.read? (L4 x) tr = some old)
      (hwi : mem.writeIn (L4 x) tr (t.views.getCoh (L4 x)) = false)
      (h0 : ¬ Ticketed t) (h1 : Ticketed oc.thread) (hk : tk oc.thread = old.toNat % 2 ^ 32)
      (hval : v.toNat = (tk oc.thread + 1) % 2 ^ 32)
      (hn : taken k oc.thread = taken k t + 1) (hw : wr k oc.thread = wr k t + 1) (hphi : phi oc.thread + 1 = phi t)
      (hv : t.views.vwOld ≤ oc.thread.views.vwOld)
      (hcase : (oc.mem = (mem.append { loc := L4 x, val := v, tid }).1 ∧ oc.thread.prom = t.prom ∧
          mem.last + 1 ≤ oc.thread.views.vwOld ∧ mem.last + 1 ≤ oc.thread.views.getCoh (L4 x) ∧
          mem.atomic (L4 x) tid tr (mem.last + 1) = true) ∨
        (∃ ts ∈ t.prom, mem.get? ts = some { loc := L4 x, val := v, tid } ∧ oc.mem = mem ∧
          oc.thread.prom = t.prom.erase ts ∧ ts ≤ oc.thread.views.getCoh (L4 x) ∧ tr < ts ∧
          mem.atomic (L4 x) tid tr ts = true))
  | st (v : Val) (htk : Ticketed oc.thread ↔ Ticketed t) (hk : Ticketed t → tk oc.thread = tk t)
      (hn : taken k oc.thread = taken k t) (hw : wr k oc.thread = wr k t + 1) (hphi : phi oc.thread = phi t)
      (hv : t.views.vwOld ≤ oc.thread.views.vwOld)
      (hcase : (oc.mem = (mem.append { loc := L4 c, val := v, tid }).1 ∧ oc.thread.prom = t.prom ∧
          mem.last + 1 ≤ oc.thread.views.vwOld) ∨
        (∃ ts ∈ t.prom, mem.get? ts = some { loc := L4 c, val := v, tid } ∧ oc.mem = mem ∧
          oc.thread.prom = t.prom.erase ts))
  | rl (v : Val) (h0 : Ticketed t) (h1 : ¬ Ticketed oc.thread) (hval : v.toNat = (tk t + 1) % 2 ^ 32)
      (hord : ORdP o t mem (tk t))
      (hn : taken k oc.thread = taken k t) (hw : wr k oc.thread = wr k t + 1) (hphi : phi oc.thread = phi t)
      (hv : t.views.vwOld ≤ oc.thread.views.vwOld)
      (hcase : (oc.mem = (mem.append { loc := L4 o, val := v, tid }).1 ∧ oc.thread.prom = t.prom ∧
          mem.last + 1 ≤ oc.thread.views.vwOld ∧ mem.last + 1 ≤ oc.thread.views.getCoh (L4 o)) ∨
        (∃ ts ∈ t.prom, mem.get? ts = some { loc := L4 o, val := v, tid } ∧ t.views.vwOld < ts ∧ oc.mem = mem ∧
          oc.thread.prom = t.prom.erase ts ∧ ts ≤ oc.thread.views.getCoh (L4 o)))

set_option hygiene false in
/-- The `TI` facts at a position that needs none of `x7`, `e7`, `f7`–`f9`,
`txn`. -/
local macro "nofacts" : term => `(fun h => absurd h (by decide))

set_option maxHeartbeats 1600000 in
/-- **One instruction step keeps `TI`**, and what it does (`Eff`). -/
theorem step_ti {k : Nat} {x o c : BitVec 64} {tid : Nat} {t : Thread isa} {mem : Memory}
    {outs : List (Except String (Outcome isa))} {oc : Outcome isa} (h : TI k x o c tid t mem)
    (hs : stepOne Arch.armv8 t tid mem = some outs) (ho : .ok oc ∈ outs) :
    TI k x o c tid oc.thread oc.mem ∧ Eff k x o c tid t mem oc := by
  have hsinv := (step_sinv h.sinv hs ho).1
  have hreg := step_reginv h.sinv h.reg hs ho
  obtain ⟨-, hcoh, -, -⟩ := stepOne_dord Arch.armv8 hs ho
  obtain ⟨-, -, hfwd, -, -, hwf⟩ := stepOne_silent_nt Arch.armv8 hs ho h.fwd
  have hwf' := hwf h.wf
  obtain ⟨hS, i, hi, hpc⟩ := h.sinv
  have hi' := hi
  simp only [tkLoopPcs, List.mem_cons, List.not_mem_nil, or_false] at hi'
  rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- 1: `MOV`
    obtain ⟨hm, hst, hpr, -⟩ := s1 hS hs ho hpc
    have hpc' : oc.thread.st.st.2 = pcA 3 := by rw [hst] <;> rfl
    have h7 : oc.thread.st.st.1.regs.X7 = t.st.st.1.regs.X7 := by rw [hst] <;> rfl
    obtain ⟨htk, hk⟩ := same_tk (by decide) (by decide) hpc hpc' (by rw [hst] <;> rfl) (by decide)
    obtain ⟨hn, hw, hph⟩ := quiet_cnt (d := 0) k (by decide) (by decide) hpc hpc' h7 (by decide) (by decide)
    refine ⟨ti_of (by decide) hpc' hsinv hreg (h7 ▸ h.k7) nofacts nofacts nofacts nofacts nofacts nofacts
      (hm ▸ pcov_quiet h.pcov hpr hcoh) hfwd hwf' (hpr ▸ h.nd), .quiet hm hpr htk hk hn hw hph ?_⟩
    exact Nat.le_of_eq (spec_done_vw _ _ (exec_mov _ (hS.at (by decide) (by decide) hpc)) hs ho).symm
  · -- 3: `CBZ`
    obtain ⟨hm, hst, hpr, -⟩ := s3 hS hs ho hpc
    have hvw := spec_done_vw _ _ (exec_cbz _ (hS.at (by decide) (by decide) hpc)) hs ho
    have h7 : oc.thread.st.st.1.regs.X7 = t.st.st.1.regs.X7 := by rw [hst] <;> rfl
    have hpq := hm ▸ pcov_quiet h.pcov hpr hcoh
    by_cases hz : w32 t.st.st.1.regs.X7 = 0#32
    · rw [ite_eq_left hz] at hst
      have hpc' : oc.thread.st.st.2 = pcA 17 := by rw [hst] <;> rfl
      obtain ⟨htk, hk⟩ := same_tk (by decide) (by decide) hpc hpc' (by rw [hst] <;> rfl) (by decide)
      obtain ⟨hn, hw, hph⟩ := quiet_cnt (d := 0) k (by decide) (by decide) hpc hpc' h7 (by decide) (by decide)
      exact ⟨ti_of (by decide) hpc' hsinv hreg (h7 ▸ h.k7) nofacts (fun _ => by rw [h7]; exact (w32_zero_iff _).mp hz)
        nofacts nofacts nofacts nofacts hpq hfwd hwf' (hpr ▸ h.nd),
        .quiet hm hpr htk hk hn hw hph (Nat.le_of_eq hvw.symm)⟩
    · rw [ite_eq_right hz] at hst
      have hpc' : oc.thread.st.st.2 = pcA 4 := by rw [hst] <;> rfl
      obtain ⟨htk, hk⟩ := same_tk (by decide) (by decide) hpc hpc' (by rw [hst] <;> rfl) (by decide)
      obtain ⟨hn, hw, hph⟩ := quiet_cnt (d := 0) k (by decide) (by decide) hpc hpc' h7 (by decide) (by decide)
      exact ⟨ti_of (by decide) hpc' hsinv hreg (h7 ▸ h.k7) (fun _ => by rw [h7]; exact fun e => hz ((w32_zero_iff _).mpr e))
        nofacts nofacts nofacts nofacts nofacts hpq hfwd hwf' (hpr ▸ h.nd),
        .quiet hm hpr htk hk hn hw hph (Nat.le_of_eq hvw.symm)⟩
  · -- 4: `LDADDA`
    have h6 := h.reg.x6' hi hpc (by decide)
    have h7n : wn t.st.st.1.regs.X7 ≠ 0 := h.x7 4 (by decide) hpc
    obtain ⟨tr, old, hst, hrd, hwi, hcase⟩ := spec_rmw_w Arch.armv8 tid rfl rfl
      (exec_ldadda _ (hS.at (by decide) (by decide) hpc) hS.x0 hS.dx) hs ho
    have hpc' : oc.thread.st.st.2 = pcA 6 := by rw [hst] <;> rfl
    have h7 : oc.thread.st.st.1.regs.X7 = t.st.st.1.regs.X7 := by rw [hst] <;> rfl
    have hk : tk oc.thread = old.toNat % 2 ^ 32 := by unfold tk; rw [hst]; exact wn_setWidth' old
    have hval : (BitVec.setWidth 128 (BitVec.setWidth 32 old + BitVec.setWidth 32 t.st.st.1.regs.X6.toBitVec)).toNat =
        (tk oc.thread + 1) % 2 ^ 32 := by
      rw [hk]
      simp only [wn] at h6
      simp only [BitVec.toNat_setWidth, BitVec.toNat_add]
      have : t.st.st.1.regs.X6.toBitVec.toNat % 2 ^ 32 = 1 := h6
      rw [this]; omega
    have h0 : ¬ Ticketed t := fun ht => absurd ((ticketed_iff hi hpc).mp ht) (by decide)
    have h1 : Ticketed oc.thread := (ticketed_iff (by decide) hpc').mpr (by decide)
    obtain ⟨a1, a2, a3⟩ := cnt_at k hi hpc
    obtain ⟨b1, b2, b3⟩ := cnt_at k (by decide) hpc'
    rw [h7] at b1 b2 b3
    simp (config := { decide := true }) only [↓reduceIte] at a1 a2 a3 b1 b2 b3
    have hn : taken k oc.thread = taken k t + 1 := by omega
    have hw : wr k oc.thread = wr k t + 1 := by omega
    have hph : phi oc.thread + 1 = phi t := by omega
    rcases hcase with ⟨hm, hpr, hvw1, hvw, hc0, hat⟩ | ⟨ts, hts, hg, -, hm, hpr, hvw, hc0, htr, hat⟩
    · have hpr' : oc.thread.prom = t.prom := hpr.trans (erase_fresh h.wf)
      refine ⟨ti_of (by decide) hpc' hsinv hreg (h7 ▸ h.k7) (fun _ => h7 ▸ h7n) nofacts nofacts nofacts nofacts
        (fun _ => ⟨mem.last + 1, fun hin => ?_, { loc := L4 x, val := _, tid }, ?_, rfl, rfl, hval⟩) ?_ hfwd hwf' (hpr' ▸ h.nd),
        .ld tr old _ hrd hwi h0 h1 hk hval hn hw hph hvw (.inl ⟨hm, hpr', hvw1, hc0, hat⟩)⟩
      · rw [hpr'] at hin; have := h.wf _ hin; omega_t
      · rw [hm]; exact Memory.get?_append_last mem _
      · rw [hm]; exact pcov_fresh h.pcov hpr' hcoh hc0
    · exact ⟨ti_of (by decide) hpc' hsinv hreg (h7 ▸ h.k7) (fun _ => h7 ▸ h7n) nofacts nofacts nofacts nofacts
        (fun _ => ⟨ts, by rw [hpr]; exact h.nd.not_mem_erase, _, hm ▸ hg, rfl, rfl, hval⟩)
        (hm ▸ pcov_ful h.pcov hg hpr hcoh hc0) hfwd hwf' (hpr ▸ h.nd.erase ts),
        .ld tr old _ hrd hwi h0 h1 hk hval hn hw hph hvw (.inr ⟨ts, hts, hg, hm, hpr, hc0, htr, hat⟩)⟩
  · -- 6: `LDAR`
    have hex := exec_ldar _ (hS.at (by decide) (by decide) hpc) hS.x1 hS.dO
    obtain ⟨tr, v, hst, hrd, hnp, -, hm, hpr, -⟩ := spec_load_np _ _ hex hs ho
    have hvw := spec_load_vw _ _ hex hs ho
    have hpc' : oc.thread.st.st.2 = pcA 7 := by rw [hst] <;> rfl
    have h7 : oc.thread.st.st.1.regs.X7 = t.st.st.1.regs.X7 := by rw [hst] <;> rfl
    obtain ⟨htk, hk⟩ := same_tk (by decide) (by decide) hpc hpc' (by rw [hst] <;> rfl) (by decide)
    obtain ⟨hn, hw, hph⟩ := quiet_cnt (d := 0) k (by decide) (by decide) hpc hpc' h7 (by decide) (by decide)
    have hp0 : mem.Prefix oc.mem := hm ▸ Memory.Prefix.refl _
    refine ⟨ti_of (by decide) hpc' hsinv hreg (h7 ▸ h.k7) (fun _ => h7 ▸ h.x7 6 (by decide) hpc) nofacts
      (fun _ => ⟨tr, v, hm ▸ hrd, ?_, hpr ▸ hnp⟩) nofacts nofacts
      (fun _ => txn_keep h.txn ((ticketed_iff hi hpc).mpr (by decide)) (hk ((ticketed_iff hi hpc).mpr (by decide)))
        hp0 (pr_eq hpr))
      (hm ▸ pcov_quiet h.pcov hpr hcoh) hfwd hwf' (hpr ▸ h.nd), .quiet hm hpr htk hk hn hw hph (Nat.le_of_eq hvw.symm)⟩
    rw [hst]; exact (wn_setWidth' v).symm
  · -- 7: `CMP`
    obtain ⟨sf, hst, hz, hm, hpr, -⟩ := s7 hS hs ho hpc
    obtain ⟨sf', hex, -⟩ := exec_cmp _ (hS.at (by decide) (by decide) hpc)
    have hvw := spec_done_vw _ _ hex hs ho
    have hpc' : oc.thread.st.st.2 = pcA 8 := by rw [hst] <;> rfl
    have h7 : oc.thread.st.st.1.regs.X7 = t.st.st.1.regs.X7 := by rw [hst] <;> rfl
    have e3 : oc.thread.st.st.1.regs.X3 = t.st.st.1.regs.X3 := by rw [hst] <;> rfl
    obtain ⟨htk, hk⟩ := same_tk (by decide) (by decide) hpc hpc' e3 (by decide)
    obtain ⟨hn, hw, hph⟩ := quiet_cnt (d := 0) k (by decide) (by decide) hpc hpc' h7 (by decide) (by decide)
    have hp0 : mem.Prefix oc.mem := hm ▸ Memory.Prefix.refl _
    refine ⟨ti_of (by decide) hpc' hsinv hreg (h7 ▸ h.k7) (fun _ => h7 ▸ h.x7 7 (by decide) hpc) nofacts nofacts
      (fun _ hz' => (h.f7 hpc).keep hp0 (pr_eq hpr) ?_) nofacts
      (fun _ => txn_keep h.txn ((ticketed_iff hi hpc).mpr (by decide)) (hk ((ticketed_iff hi hpc).mpr (by decide)))
        hp0 (pr_eq hpr))
      (hm ▸ pcov_quiet h.pcov hpr hcoh) hfwd hwf' (hpr ▸ h.nd), .quiet hm hpr htk hk hn hw hph (Nat.le_of_eq hvw.symm)⟩
    have hz'' : sf.z = true := by rw [hst] at hz'; exact hz'
    rw [e3]; exact hz.mp hz''
  · -- 8: `B.NE`
    obtain ⟨hm, hst, hpr, -⟩ := s8 hS hs ho hpc
    have hvw := spec_done_vw _ _ (exec_bne _ (hS.at (by decide) (by decide) hpc)) hs ho
    have h7 : oc.thread.st.st.1.regs.X7 = t.st.st.1.regs.X7 := by rw [hst] <;> rfl
    have e3 : oc.thread.st.st.1.regs.X3 = t.st.st.1.regs.X3 := by rw [hst] <;> rfl
    have hp0 : mem.Prefix oc.mem := hm ▸ Memory.Prefix.refl _
    have hT : Ticketed t := (ticketed_iff hi hpc).mpr (by decide)
    by_cases hz : t.st.st.1.status.z = true
    · rw [ite_eq_left hz] at hst
      have hpc' : oc.thread.st.st.2 = pcA 9 := by rw [hst] <;> rfl
      obtain ⟨htk, hk⟩ := same_tk (by decide) (by decide) hpc hpc' e3 (by decide)
      obtain ⟨hn, hw, hph⟩ := quiet_cnt (d := 0) k (by decide) (by decide) hpc hpc' h7 (by decide) (by decide)
      exact ⟨ti_of (by decide) hpc' hsinv hreg (h7 ▸ h.k7) (fun _ => h7 ▸ h.x7 8 (by decide) hpc) nofacts nofacts
        nofacts (fun _ => (h.f8 hpc hz).keep hp0 (pr_eq hpr) (by rw [e3]))
        (fun _ => txn_keep h.txn hT (hk hT) hp0 (pr_eq hpr))
        (hm ▸ pcov_quiet h.pcov hpr hcoh) hfwd hwf' (hpr ▸ h.nd), .quiet hm hpr htk hk hn hw hph (Nat.le_of_eq hvw.symm)⟩
    · rw [ite_eq_right hz] at hst
      have hpc' : oc.thread.st.st.2 = pcA 6 := by rw [hst] <;> rfl
      obtain ⟨htk, hk⟩ := same_tk (by decide) (by decide) hpc hpc' e3 (by decide)
      obtain ⟨hn, hw, hph⟩ := quiet_cnt (d := 0) k (by decide) (by decide) hpc hpc' h7 (by decide) (by decide)
      exact ⟨ti_of (by decide) hpc' hsinv hreg (h7 ▸ h.k7) (fun _ => h7 ▸ h.x7 8 (by decide) hpc) nofacts nofacts
        nofacts nofacts (fun _ => txn_keep h.txn hT (hk hT) hp0 (pr_eq hpr))
        (hm ▸ pcov_quiet h.pcov hpr hcoh) hfwd hwf' (hpr ▸ h.nd), .quiet hm hpr htk hk hn hw hph (Nat.le_of_eq hvw.symm)⟩
  · -- 9: `LDR`
    have hex := exec_ldr_c _ (hS.at (by decide) (by decide) hpc) hS.x2 hS.dc
    obtain ⟨v, hst, hm, hpr, -⟩ := s9 hS hs ho hpc
    have hvw := spec_load_vw _ _ hex hs ho
    have hpc' : oc.thread.st.st.2 = pcA 10 := by rw [hst] <;> rfl
    have h7 : oc.thread.st.st.1.regs.X7 = t.st.st.1.regs.X7 := by rw [hst] <;> rfl
    have e3 : oc.thread.st.st.1.regs.X3 = t.st.st.1.regs.X3 := by rw [hst] <;> rfl
    have hp0 : mem.Prefix oc.mem := hm ▸ Memory.Prefix.refl _
    have hT : Ticketed t := (ticketed_iff hi hpc).mpr (by decide)
    obtain ⟨htk, hk⟩ := same_tk (by decide) (by decide) hpc hpc' e3 (by decide)
    obtain ⟨hn, hw, hph⟩ := quiet_cnt (d := 0) k (by decide) (by decide) hpc hpc' h7 (by decide) (by decide)
    exact ⟨ti_of (by decide) hpc' hsinv hreg (h7 ▸ h.k7) (fun _ => h7 ▸ h.x7 9 (by decide) hpc) nofacts nofacts
      nofacts (fun _ => (h.f9 9 (by decide) hpc).keep hp0 (pr_eq hpr) (by rw [e3]))
      (fun _ => txn_keep h.txn hT (hk hT) hp0 (pr_eq hpr))
      (hm ▸ pcov_quiet h.pcov hpr hcoh) hfwd hwf' (hpr ▸ h.nd), .quiet hm hpr htk hk hn hw hph (Nat.le_of_eq hvw.symm)⟩
  · -- 10: `ADD W5`
    obtain ⟨hm, hst, hpr, -⟩ := s10 hS hs ho hpc
    have hvw := spec_done_vw _ _ (exec_add5 _ (hS.at (by decide) (by decide) hpc)) hs ho
    have hpc' : oc.thread.st.st.2 = pcA 11 := by rw [hst] <;> rfl
    have h7 : oc.thread.st.st.1.regs.X7 = t.st.st.1.regs.X7 := by rw [hst] <;> rfl
    have e3 : oc.thread.st.st.1.regs.X3 = t.st.st.1.regs.X3 := by rw [hst] <;> rfl
    have hp0 : mem.Prefix oc.mem := hm ▸ Memory.Prefix.refl _
    have hT : Ticketed t := (ticketed_iff hi hpc).mpr (by decide)
    obtain ⟨htk, hk⟩ := same_tk (by decide) (by decide) hpc hpc' e3 (by decide)
    obtain ⟨hn, hw, hph⟩ := quiet_cnt (d := 0) k (by decide) (by decide) hpc hpc' h7 (by decide) (by decide)
    exact ⟨ti_of (by decide) hpc' hsinv hreg (h7 ▸ h.k7) (fun _ => h7 ▸ h.x7 10 (by decide) hpc) nofacts nofacts
      nofacts (fun _ => (h.f9 10 (by decide) hpc).keep hp0 (pr_eq hpr) (by rw [e3]))
      (fun _ => txn_keep h.txn hT (hk hT) hp0 (pr_eq hpr))
      (hm ▸ pcov_quiet h.pcov hpr hcoh) hfwd hwf' (hpr ▸ h.nd), .quiet hm hpr htk hk hn hw hph (Nat.le_of_eq hvw.symm)⟩
  · -- 11: `STR`
    obtain ⟨hst, hcase⟩ := spec_store_c _ _ (exec_str_c _ (hS.at (by decide) (by decide) hpc) hS.x2 hS.dc) hs ho
    have hpc' : oc.thread.st.st.2 = pcA 12 := by rw [hst] <;> rfl
    have h7 : oc.thread.st.st.1.regs.X7 = t.st.st.1.regs.X7 := by rw [hst] <;> rfl
    have e3 : oc.thread.st.st.1.regs.X3 = t.st.st.1.regs.X3 := by rw [hst] <;> rfl
    have hT : Ticketed t := (ticketed_iff hi hpc).mpr (by decide)
    obtain ⟨htk, hk⟩ := same_tk (by decide) (by decide) hpc hpc' e3 (by decide)
    obtain ⟨hn, hw, hph⟩ := quiet_cnt (d := 1) k (by decide) (by decide) hpc hpc' h7 (by decide) (by decide)
    rcases hcase with ⟨hm, hpr, hvw1, hvw, hc0⟩ | ⟨ts, hts, hg, -, -, hm, hpr, hvw, hc0⟩
    · have hpr' : oc.thread.prom = t.prom := hpr.trans (erase_fresh h.wf)
      have hp0 : mem.Prefix oc.mem := hm ▸ Memory.Prefix.append _ _
      exact ⟨ti_of (by decide) hpc' hsinv hreg (h7 ▸ h.k7) (fun _ => h7 ▸ h.x7 11 (by decide) hpc) nofacts nofacts
        nofacts (fun _ => (h.f9 11 (by decide) hpc).keep hp0 (pr_eq hpr') (by rw [e3]))
        (fun _ => txn_keep h.txn hT (hk hT) hp0 (pr_eq hpr'))
        (hm ▸ pcov_fresh h.pcov hpr' hcoh hc0) hfwd hwf' (hpr' ▸ h.nd),
        .st _ htk hk hn hw hph hvw (.inl ⟨hm, hpr', hvw1 rfl⟩)⟩
    · have hp0 : mem.Prefix oc.mem := hm ▸ Memory.Prefix.refl _
      exact ⟨ti_of (by decide) hpc' hsinv hreg (h7 ▸ h.k7) (fun _ => h7 ▸ h.x7 11 (by decide) hpc) nofacts nofacts
        nofacts (fun _ => (h.f9 11 (by decide) hpc).keep hp0 (pr_erase hpr) (by rw [e3]))
        (fun _ => txn_keep h.txn hT (hk hT) hp0 (pr_erase hpr))
        (hm ▸ pcov_ful h.pcov hg hpr hcoh hc0) hfwd hwf' (hpr ▸ h.nd.erase ts),
        .st _ htk hk hn hw hph hvw (.inr ⟨ts, hts, hg, hm, hpr⟩)⟩
  · -- 12: `ADD W4`
    obtain ⟨hm, hst, hpr, -⟩ := s12 hS hs ho hpc
    have hvw := spec_done_vw _ _ (exec_add4 _ (hS.at (by decide) (by decide) hpc)) hs ho
    have hpc' : oc.thread.st.st.2 = pcA 13 := by rw [hst] <;> rfl
    have h7 : oc.thread.st.st.1.regs.X7 = t.st.st.1.regs.X7 := by rw [hst] <;> rfl
    have e3 : oc.thread.st.st.1.regs.X3 = t.st.st.1.regs.X3 := by rw [hst] <;> rfl
    have hp0 : mem.Prefix oc.mem := hm ▸ Memory.Prefix.refl _
    have hT : Ticketed t := (ticketed_iff hi hpc).mpr (by decide)
    obtain ⟨htk, hk⟩ := same_tk (by decide) (by decide) hpc hpc' e3 (by decide)
    obtain ⟨hn, hw, hph⟩ := quiet_cnt (d := 0) k (by decide) (by decide) hpc hpc' h7 (by decide) (by decide)
    exact ⟨ti_of (by decide) hpc' hsinv hreg (h7 ▸ h.k7) (fun _ => h7 ▸ h.x7 12 (by decide) hpc) nofacts nofacts
      nofacts (fun _ => (h.f9 12 (by decide) hpc).keep hp0 (pr_eq hpr) (by rw [e3]))
      (fun _ => txn_keep h.txn hT (hk hT) hp0 (pr_eq hpr))
      (hm ▸ pcov_quiet h.pcov hpr hcoh) hfwd hwf' (hpr ▸ h.nd), .quiet hm hpr htk hk hn hw hph (Nat.le_of_eq hvw.symm)⟩
  · -- 13: `STLR`
    obtain ⟨hst, hcase⟩ := spec_store_c _ _ (exec_stlr _ (hS.at (by decide) (by decide) hpc) hS.x1 hS.dO) hs ho
    have hpc' : oc.thread.st.st.2 = pcA 14 := by rw [hst] <;> rfl
    have h7 : oc.thread.st.st.1.regs.X7 = t.st.st.1.regs.X7 := by rw [hst] <;> rfl
    have h0 : Ticketed t := (ticketed_iff hi hpc).mpr (by decide)
    have h1 : ¬ Ticketed oc.thread := fun ht => absurd ((ticketed_iff (by decide) hpc').mp ht) (by decide)
    have hval : (BitVec.setWidth 128 (BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec)).toNat = (tk t + 1) % 2 ^ 32 := by
      rw [val_setWidth']; exact h.reg.x4 hpc
    have hord : ORdP o t mem (tk t) := h.f9 13 (by decide) hpc
    obtain ⟨hn, hw, hph⟩ := quiet_cnt (d := 1) k (by decide) (by decide) hpc hpc' h7 (by decide) (by decide)
    have hx7 : 14 ∈ [4, 6, 7, 8, 9, 10, 11, 12, 13, 14] → wn oc.thread.st.st.1.regs.X7 ≠ 0 :=
      fun _ => h7 ▸ h.x7 13 (by decide) hpc
    rcases hcase with ⟨hm, hpr, hvw1, hvw, hc0⟩ | ⟨ts, hts, hg, -, hrel, hm, hpr, hvw, hc0⟩
    · have hpr' : oc.thread.prom = t.prom := hpr.trans (erase_fresh h.wf)
      exact ⟨ti_of (by decide) hpc' hsinv hreg (h7 ▸ h.k7) hx7 nofacts nofacts nofacts nofacts nofacts
        (hm ▸ pcov_fresh h.pcov hpr' hcoh hc0) hfwd hwf' (hpr' ▸ h.nd),
        .rl _ h0 h1 hval hord hn hw hph hvw (.inl ⟨hm, hpr', hvw1 rfl, hc0⟩)⟩
    · exact ⟨ti_of (by decide) hpc' hsinv hreg (h7 ▸ h.k7) hx7 nofacts nofacts nofacts nofacts nofacts
        (hm ▸ pcov_ful h.pcov hg hpr hcoh hc0) hfwd hwf' (hpr ▸ h.nd.erase ts),
        .rl _ h0 h1 hval hord hn hw hph hvw (.inr ⟨ts, hts, hg, hrel rfl, hm, hpr, hc0⟩)⟩
  · -- 14: `SUB`
    obtain ⟨hm, hst, hpr, -⟩ := s14 hS hs ho hpc
    have hvw := spec_done_vw _ _ (exec_sub _ (hS.at (by decide) (by decide) hpc)) hs ho
    have hpc' : oc.thread.st.st.2 = pcA 15 := by rw [hst] <;> rfl
    have h7n : wn t.st.st.1.regs.X7 ≠ 0 := h.x7 14 (by decide) hpc
    have h7 : wn oc.thread.st.st.1.regs.X7 = wn t.st.st.1.regs.X7 - 1 := by
      rw [← wn_sub1 _ h7n, hst]; rfl
    obtain ⟨htk, hk⟩ := same_tk (by decide) (by decide) hpc hpc' (by rw [hst] <;> rfl) (by decide)
    obtain ⟨a1, a2, a3⟩ := cnt_at k hi hpc
    obtain ⟨b1, b2, b3⟩ := cnt_at k (by decide) hpc'
    rw [h7] at b1 b2 b3
    simp (config := { decide := true }) only [↓reduceIte] at a1 a2 a3 b1 b2 b3
    have hk7 := h.k7
    exact ⟨ti_of (by decide) hpc' hsinv hreg (by omega) nofacts nofacts nofacts nofacts nofacts nofacts
      (hm ▸ pcov_quiet h.pcov hpr hcoh) hfwd hwf' (hpr ▸ h.nd),
      .quiet hm hpr htk hk (by omega) (by omega) (by omega) (Nat.le_of_eq hvw.symm)⟩
  · -- 15: `B round`
    obtain ⟨hm, hst, hpr, -⟩ := s15 hS hs ho hpc
    have hvw := spec_done_vw _ _ (exec_b_round _ (hS.at (by decide) (by decide) hpc)) hs ho
    have hpc' : oc.thread.st.st.2 = pcA 3 := by rw [hst] <;> rfl
    have h7 : oc.thread.st.st.1.regs.X7 = t.st.st.1.regs.X7 := by rw [hst] <;> rfl
    obtain ⟨htk, hk⟩ := same_tk (by decide) (by decide) hpc hpc' (by rw [hst] <;> rfl) (by decide)
    obtain ⟨hn, hw, hph⟩ := quiet_cnt (d := 0) k (by decide) (by decide) hpc hpc' h7 (by decide) (by decide)
    exact ⟨ti_of (by decide) hpc' hsinv hreg (h7 ▸ h.k7) nofacts nofacts nofacts nofacts nofacts nofacts
      (hm ▸ pcov_quiet h.pcov hpr hcoh) hfwd hwf' (hpr ▸ h.nd), .quiet hm hpr htk hk hn hw hph (Nat.le_of_eq hvw.symm)⟩
  · rw [stepOne_end hS hpc] at hs; cases hs

/-! ## The certification analysis -/

/-- Distinct `next` messages have distinct values. -/
def XInj (x : BitVec 64) (mem : Memory) : Prop :=
  ∀ ts1 ts2 w1 w2, mem.get? ts1 = some w1 → mem.get? ts2 = some w2 → w1.loc = L4 x → w2.loc = L4 x →
    w1.val.toNat = w2.val.toNat → ts1 = ts2

/-- The thread's outstanding promises of `next` messages. -/
def countXP (x : BitVec 64) (t : Thread isa) (mem : Memory) : Nat :=
  t.prom.countP fun ts => (mem.get? ts).any (·.loc == L4 x)

theorem countXP_mono {x : BitVec 64} {t : Thread isa} {mem mem' : Memory} (hp : mem.Prefix mem')
    (hwf : ∀ p ∈ t.prom, p ≤ mem.last) : countXP x t mem' = countXP x t mem :=
  List.countP_congr fun ts h => by rw [hp.get? (hwf ts h)]

theorem countXP_erase {x : BitVec 64} {t t' : Thread isa} {mem : Memory} {ts : Time} {w : Msg}
    (hp : t'.prom = t.prom.erase ts) (hin : ts ∈ t.prom) (hg : mem.get? ts = some w) :
    countXP x t mem = countXP x t' mem + (if w.loc = L4 x then 1 else 0) := by
  unfold countXP
  rw [hp, (List.perm_cons_erase hin).countP_eq, List.countP_cons, hg]
  by_cases h : w.loc = L4 x <;> simp [h]

theorem Eff.vw {k : Nat} {x o c : BitVec 64} {tid : Nat} {t : Thread isa} {mem : Memory} {oc : Outcome isa}
    (he : Eff k x o c tid t mem oc) : t.views.vwOld ≤ oc.thread.views.vwOld := by
  cases he <;> assumption

/-- **Lemma B: a certifiable worker has at most as many `next` promises as
`LDADDA`s left.** -/
theorem cert_cnt {k : Nat} {x o c : BitVec 64} {tid n : Nat} {p q : Thread isa × Memory}
    (hr : ThreadNPn Arch.armv8 tid n p q) (hq : q.1.prom = []) (hti : TI k x o c tid p.1 p.2)
    (hxo : L4 x ≠ L4 o) (hxc : L4 x ≠ L4 c) : countXP x p.1 p.2 ≤ phi p.1 := by
  induction hr with
  | refl n p => simp [countXP, hq]
  | @step n p q r hs _ ih =>
    obtain ⟨outs, oc, hs, ho, rfl⟩ := hs
    obtain ⟨hti', he⟩ := step_ti hti hs ho
    have ih := ih hq hti'
    dsimp only at ih
    have hwf := hti.wf
    cases he with
    | quiet hm hp _ _ _ _ hphi _ =>
      rw [hm] at ih; unfold countXP at ih ⊢; rw [hp, hphi] at ih; exact ih
    | ld tr old v hrd hwi h0 h1 hk hval hn hw hphi hv hcase =>
      rcases hcase with ⟨hm, hp, -⟩ | ⟨ts, hts, hg, hm, hp, -⟩
      · rw [hm, countXP_mono (Memory.Prefix.append _ _) fun a ha => hwf a (hp ▸ ha)] at ih
        unfold countXP at ih ⊢; rw [hp] at ih; omega
      · rw [hm] at ih
        have := countXP_erase (x := x) hp hts hg
        simp only [↓reduceIte] at this
        omega
    | st v htk hk hn hw hphi hv hcase =>
      rcases hcase with ⟨hm, hp, -⟩ | ⟨ts, hts, hg, hm, hp⟩
      · rw [hm, countXP_mono (Memory.Prefix.append _ _) fun a ha => hwf a (hp ▸ ha)] at ih
        unfold countXP at ih ⊢; rw [hp, hphi] at ih; exact ih
      · rw [hm] at ih
        have := countXP_erase (x := x) hp hts hg
        simp only [Ne.symm hxc, ↓reduceIte] at this
        omega
    | rl v h0 h1 hval hord hn hw hphi hv hcase =>
      rcases hcase with ⟨hm, hp, -⟩ | ⟨ts, hts, hg, -, hm, hp, -⟩
      · rw [hm, countXP_mono (Memory.Prefix.append _ _) fun a ha => hwf a (hp ▸ ha)] at ih
        unfold countXP at ih ⊢; rw [hp, hphi] at ih; exact ih
      · rw [hm] at ih
        have := countXP_erase (x := x) hp hts hg
        simp only [Ne.symm hxo, ↓reduceIte] at this
        omega

/-- **An outstanding `owner` promise lies above `vwOld`** in a run that
empties the promise set (`STLR` fulfils only above `vwOld`, which only grows). -/
theorem vw_run {k : Nat} {x o c : BitVec 64} {tid n : Nat} {p q : Thread isa × Memory}
    (hr : ThreadNPn Arch.armv8 tid n p q) (hq : q.1.prom = []) (hti : TI k x o c tid p.1 p.2)
    (hxo : L4 x ≠ L4 o) (hoc : L4 o ≠ L4 c) {ts : Time} {w : Msg} (hin : ts ∈ p.1.prom)
    (hg : p.2.get? ts = some w) (hl : w.loc = L4 o) : p.1.views.vwOld < ts := by
  induction hr with
  | refl n p => rw [hq] at hin; cases hin
  | @step n p q r hs _ ih =>
    obtain ⟨outs, oc, hs, ho, rfl⟩ := hs
    obtain ⟨hti', he⟩ := step_ti hti hs ho
    have hg' : oc.mem.get? ts = some w := by rw [(Memory.Prefix.stepOne hs ho).get? (hti.wf ts hin)]; exact hg
    by_cases hst : ts ∈ oc.thread.prom
    · exact Nat.lt_of_le_of_lt he.vw (ih hq hti' hst hg')
    · cases he with
      | quiet _ hp => exact absurd (hp ▸ hin) hst
      | ld tr old v hrd hwi h0 h1 hk hval hn hw hphi hv hcase =>
        rcases hcase with ⟨-, hp, -⟩ | ⟨ts0, -, hg0, -, hp, -⟩
        · exact absurd (hp ▸ hin) hst
        · refine absurd (hp ▸ (List.mem_erase_of_ne fun e => ?_).mpr hin) hst
          subst e; rw [hg] at hg0; cases hg0; exact hxo hl
      | st v htk hk hn hw hphi hv hcase =>
        rcases hcase with ⟨-, hp, -⟩ | ⟨ts0, -, hg0, -, hp⟩
        · exact absurd (hp ▸ hin) hst
        · refine absurd (hp ▸ (List.mem_erase_of_ne fun e => ?_).mpr hin) hst
          subst e; rw [hg] at hg0; cases hg0; exact hoc hl.symm
      | rl v h0 h1 hval hord hn hw hphi hv hcase =>
        rcases hcase with ⟨-, hp, -⟩ | ⟨ts0, -, hg0, hlt, -, hp, -⟩
        · exact absurd (hp ▸ hin) hst
        · by_cases e : ts = ts0
          · subst e; exact hlt
          · exact absurd (hp ▸ (List.mem_erase_of_ne e).mpr hin) hst

theorem XMsg.back {x : BitVec 64} {tid : Nat} {mem mem' : Memory} {ts : Time} {v : Nat} (h : XMsg x tid mem' ts v)
    (hp : mem.Prefix mem') (hle : ts ≤ mem.last) : XMsg x tid mem ts v := by
  obtain ⟨w, hw, h1⟩ := h
  exact ⟨w, by rw [← hp.get? hle]; exact hw, h1⟩

theorem append_ne (mem : Memory) (w : Msg) : (mem.append w).1 ≠ mem := fun h => by
  have := congrArg Memory.last h
  rw [Memory.last_append] at this
  omega_t

/-- **A certified `next` promise is an atomic increment of the last `next`
message below it**: the fulfilling `LDADDA` reads `tr` with no write to `next`
in `(tr, coh]`; a `next` message in `(tr, ts)` is the thread's (atomicity),
above its `coh`, hence an outstanding promise (`PCov`), which is dead after
the fulfilment of `ts` (`coh_lt_of_certOkN`). -/
theorem cert_x {k : Nat} {x o c : BitVec 64} {tid n : Nat} {p q : Thread isa × Memory}
    (hr : ThreadNPn Arch.armv8 tid n p q) (hq : q.1.prom = []) (hti : TI k x o c tid p.1 p.2)
    (hxo : L4 x ≠ L4 o) (hxc : L4 x ≠ L4 c) {ts : Time} {w : Msg} (hin : ts ∈ p.1.prom)
    (hg : p.2.get? ts = some w) (hl : w.loc = L4 x) :
    ∃ tr old, tr < ts ∧ p.2.read? (L4 x) tr = some old ∧ w.val.toNat = (old.toNat % 2 ^ 32 + 1) % 2 ^ 32 ∧
      ∀ ts' w', p.2.get? ts' = some w' → w'.loc = L4 x → tr < ts' → ts' < ts → False := by
  induction hr with
  | refl n p => rw [hq] at hin; cases hin
  | @step n p q r hs hrest ih =>
    obtain ⟨outs, oc, hs, ho, rfl⟩ := hs
    obtain ⟨hti', he⟩ := step_ti hti hs ho
    have hP := Memory.Prefix.stepOne hs ho
    have hle := hti.wf ts hin
    have hg' : oc.mem.get? ts = some w := by rw [hP.get? hle]; exact hg
    by_cases hst : ts ∈ oc.thread.prom
    · obtain ⟨tr, old, h1, h2, h3, h4⟩ := ih hq hti' hst hg'
      refine ⟨tr, old, h1, by rw [← hP.read? (by omega_t)]; exact h2, h3, fun ts' w' a b c d => h4 ts' w' ?_ b c d⟩
      rw [hP.get? (by omega_t)]; exact a
    · cases he with
      | quiet _ hp => exact absurd (hp ▸ hin) hst
      | ld tr old v hrd hwi h0 h1 hk hval hn hw hphi hv hcase =>
        rcases hcase with ⟨-, hp, -⟩ | ⟨ts0, -, hg0, hm, hp, hc0, htr, hat⟩
        · exact absurd (hp ▸ hin) hst
        · by_cases e : ts = ts0
          · subst e
            rw [hg] at hg0; cases hg0
            refine ⟨tr, old, htr, hrd, by show v.toNat = _; rw [hval, hk], fun ts' w' a b c d => ?_⟩
            have hid := Memory.atomic_elim hat hrd ts' w' c d a b
            have hcoh : p.1.views.getCoh (L4 x) < ts' := by
              refine Nat.lt_of_not_le fun hh => ?_
              have := (Memory.writeIn_iff _ _ _ _).mpr ⟨ts', w', c, hh, a, b⟩
              rw [hwi] at this; cases this
            have hin' := hti.pcov ts' w' a hid (b ▸ hcoh)
            have hin'' : ts' ∈ oc.thread.prom := hp ▸ (List.mem_erase_of_ne (by omega_t)).mpr hin'
            have := coh_lt_of_certOkN ⟨_, _, hrest, hq⟩ hin'' (by rw [hm]; exact a)
            rw [b] at this; omega_t
          · exact absurd (hp ▸ (List.mem_erase_of_ne e).mpr hin) hst
      | st v htk hk hn hw hphi hv hcase =>
        rcases hcase with ⟨-, hp, -⟩ | ⟨ts0, -, hg0, -, hp⟩
        · exact absurd (hp ▸ hin) hst
        · refine absurd (hp ▸ (List.mem_erase_of_ne fun e => ?_).mpr hin) hst
          subst e; rw [hg] at hg0; cases hg0; exact hxc hl.symm
      | rl v h0 h1 hval hord hn hw hphi hv hcase =>
        rcases hcase with ⟨-, hp, -⟩ | ⟨ts0, -, hg0, -, -, hp, -⟩
        · exact absurd (hp ▸ hin) hst
        · refine absurd (hp ▸ (List.mem_erase_of_ne fun e => ?_).mpr hin) hst
          subst e; rw [hg] at hg0; cases hg0; exact hxo hl.symm

/-- Two `next` messages of a ticketed thread with its ticket's value: one is
not outstanding (`txn`), so the other is not either (`XInj`). -/
theorem txn_absurd {k : Nat} {x o c : BitVec 64} {tid : Nat} {t : Thread isa} {mem : Memory}
    (hti : TI k x o c tid t mem) (h0 : Ticketed t) (hxi : XInj x mem) {ts2 : Time} (h2 : ts2 ∈ t.prom)
    (hx : XMsg x tid mem ts2 ((tk t + 1) % 2 ^ 32)) : False := by
  obtain ⟨ts1, hn, w1, hg1, hl1, -, hv1⟩ := hti.txn h0
  obtain ⟨w2, hg2, hl2, -, hv2⟩ := hx
  exact hn (hxi ts1 ts2 w1 w2 hg1 hg2 hl1 hl2 (hv1.trans hv2.symm) ▸ h2)

/-- **One step keeps `OH`**, given, for a fresh `LDADDA`, that the thread's
`owner` messages of its new ticket's value are outstanding (`hld`). -/
theorem oh_step {k : Nat} {x o c : BitVec 64} {tid : Nat} {t : Thread isa} {mem : Memory} {oc : Outcome isa}
    (hti : TI k x o c tid t mem) (hoh : OH x o tid t mem) (hxi : XInj x mem) (he : Eff k x o c tid t mem oc)
    (hxo : L4 x ≠ L4 o) (hoc : L4 o ≠ L4 c)
    (hld : oc.mem ≠ mem → ¬ Ticketed t → Ticketed oc.thread → ∀ ts w, mem.get? ts = some w → w.loc = L4 o →
      w.tid = tid → w.val.toNat = (tk oc.thread + 1) % 2 ^ 32 → ts ∈ t.prom) :
    OH x o tid oc.thread oc.mem := by
  intro ts w hw hlo hid v hv hH
  cases he with
  | quiet hm hp htk hk _ _ _ _ =>
    rw [hm] at hw hH; rw [hp]
    refine hoh ts w hw hlo hid v hv ?_
    rcases hH with ⟨ht, htk'⟩ | ⟨ts2, h2, hx⟩
    · exact .inl ⟨htk.mp ht, (hk (htk.mp ht)).symm.trans htk'⟩
    · exact .inr ⟨ts2, hp ▸ h2, hx⟩
  | ld tr old vv hrd hwi h0 h1 hk hval hn hw' hphi hv' hcase =>
    rcases hcase with ⟨hm, hp, -⟩ | ⟨ts0, hts0, hg0, hm, hp, -⟩
    · rw [hm] at hw hH; rw [hp]
      rcases mem.get?_append_eq_some _ hw with ⟨-, hw1⟩ | ⟨-, rfl⟩
      · rcases hH with ⟨-, htk'⟩ | ⟨ts2, h2, hx⟩
        · exact hld (by rw [hm]; exact append_ne _ _) h0 h1 ts w hw1 hlo hid (htk' ▸ hv)
        · exact hoh ts w hw1 hlo hid v hv
            (.inr ⟨ts2, hp ▸ h2, hx.back (Memory.Prefix.append _ _) (hti.wf ts2 (hp ▸ h2))⟩)
      · exact absurd hlo hxo
    · rw [hm] at hw hH; rw [hp]
      have hne : ts ≠ ts0 := fun e => by subst e; rw [hw] at hg0; cases hg0; exact hxo hlo
      refine (List.mem_erase_of_ne hne).mpr (hoh ts w hw hlo hid v hv ?_)
      rcases hH with ⟨-, htk'⟩ | ⟨ts2, h2, hx⟩
      · exact .inr ⟨ts0, hts0, _, hg0, rfl, rfl, by rw [hval, htk']⟩
      · exact .inr ⟨ts2, List.mem_of_mem_erase (hp ▸ h2), hx⟩
  | st vv htk hk hn hw' hphi hv' hcase =>
    have hH' : ∀ (hpr : ∀ a ∈ oc.thread.prom, a ∈ t.prom) (hP : mem.Prefix oc.mem), HoldsV x tid t mem v := by
      intro hpr hP
      rcases hH with ⟨ht, htk'⟩ | ⟨ts2, h2, hx⟩
      · exact .inl ⟨htk.mp ht, (hk (htk.mp ht)).symm.trans htk'⟩
      · exact .inr ⟨ts2, hpr _ h2, hx.back hP (hti.wf ts2 (hpr _ h2))⟩
    rcases hcase with ⟨hm, hp, -⟩ | ⟨ts0, hts0, hg0, hm, hp⟩
    · have hH1 := hH' (fun a h => hp ▸ h) (hm ▸ Memory.Prefix.append _ _)
      rw [hm] at hw; rw [hp]
      rcases mem.get?_append_eq_some _ hw with ⟨-, hw1⟩ | ⟨-, rfl⟩
      · exact hoh ts w hw1 hlo hid v hv hH1
      · exact absurd hlo.symm hoc
    · have hH1 := hH' (fun a h => List.mem_of_mem_erase (hp ▸ h)) (hm ▸ Memory.Prefix.refl _)
      rw [hm] at hw; rw [hp]
      have hne : ts ≠ ts0 := fun e => by subst e; rw [hw] at hg0; cases hg0; exact hoc hlo.symm
      exact (List.mem_erase_of_ne hne).mpr (hoh ts w hw hlo hid v hv hH1)
  | rl vv h0 h1 hval hord hn hw' hphi hv' hcase =>
    rcases hH with ⟨ht, -⟩ | ⟨ts2, h2, hx⟩
    · exact absurd ht h1
    rcases hcase with ⟨hm, hp, -⟩ | ⟨ts0, hts0, hg0, -, hm, hp, -⟩
    · rw [hm] at hw hx; rw [hp]
      have h2' : ts2 ∈ t.prom := hp ▸ h2
      have hx' := hx.back (Memory.Prefix.append _ _) (hti.wf ts2 h2')
      rcases mem.get?_append_eq_some _ hw with ⟨-, hw1⟩ | ⟨-, rfl⟩
      · exact hoh ts w hw1 hlo hid v hv (.inr ⟨ts2, h2', hx'⟩)
      · exact (txn_absurd hti h0 hxi h2' (by rw [← hval]; exact hv ▸ hx')).elim
    · rw [hm] at hw hx; rw [hp]
      have h2' : ts2 ∈ t.prom := List.mem_of_mem_erase (hp ▸ h2)
      have hne : ts ≠ ts0 := fun e => by
        subst e; rw [hw] at hg0; cases hg0
        exact txn_absurd hti h0 hxi h2' (by rw [← hval]; exact hv ▸ hx)
      exact (List.mem_erase_of_ne hne).mpr (hoh ts w hw hlo hid v hv (.inr ⟨ts2, h2', hx⟩))

/-- **A certified `owner` promise** `ts` (the last message): no fresh write
comes before its fulfilment (`vw_run`), which is an `STLR` at a ticket `kk`
read from a readable `owner` message and taken with a `next` message of
value `kk + 1`; no other `owner` message of the thread has the value `kk + 1`
(it would be outstanding by `OH`, and dead after the fulfilment of `ts`). -/
theorem cert_o {k : Nat} {x o c : BitVec 64} {tid n : Nat} {p q : Thread isa × Memory}
    (hr : ThreadNPn Arch.armv8 tid n p q) (hq : q.1.prom = []) (hti : TI k x o c tid p.1 p.2)
    (hoh : OH x o tid p.1 p.2) (hxi : XInj x p.2) (hxo : L4 x ≠ L4 o) (hoc : L4 o ≠ L4 c) {ts : Time} {w : Msg}
    (hin : ts ∈ p.1.prom) (hg : p.2.get? ts = some w) (hl : w.loc = L4 o) (hlast : ts = p.2.last) :
    ∃ kk tr v, p.2.read? (L4 o) tr = some v ∧ v.toNat % 2 ^ 32 = kk ∧ w.val.toNat = (kk + 1) % 2 ^ 32 ∧
      (∃ ts1, XMsg x tid p.2 ts1 ((kk + 1) % 2 ^ 32)) ∧
      ∀ ts' w', p.2.get? ts' = some w' → w'.loc = L4 o → w'.tid = tid → w'.val.toNat = (kk + 1) % 2 ^ 32 →
        ts' = ts := by
  induction hr with
  | refl n p => rw [hq] at hin; cases hin
  | @step n p q r hs hrest ih =>
    obtain ⟨outs, oc, hs, ho, rfl⟩ := hs
    obtain ⟨hti', he⟩ := step_ti hti hs ho
    have hP := Memory.Prefix.stepOne hs ho
    have hle := hti.wf ts hin
    have hg' : oc.mem.get? ts = some w := by rw [hP.get? hle]; exact hg
    have hnf : p.2.last + 1 ≤ oc.thread.views.vwOld → ts ∈ oc.thread.prom → False := fun h1 h2 =>
      absurd (vw_run hrest hq hti' hxo hoc h2 hg' hl) (by omega_t)
    have hm : oc.mem = p.2 := by
      cases he with
      | quiet hm => exact hm
      | ld tr old vv hrd hwi h0 h1 hk hval hn hw hphi hv hcase =>
        rcases hcase with ⟨-, hp, h1, -⟩ | ⟨ts0, -, -, hm, -⟩
        · exact (hnf h1 (hp ▸ hin)).elim
        · exact hm
      | st vv htk hk hn hw hphi hv hcase =>
        rcases hcase with ⟨-, hp, h1⟩ | ⟨ts0, -, -, hm, -⟩
        · exact (hnf h1 (hp ▸ hin)).elim
        · exact hm
      | rl vv h0 h1 hval hord hn hw hphi hv hcase =>
        rcases hcase with ⟨-, hp, h1, -⟩ | ⟨ts0, -, -, -, hm, -⟩
        · exact (hnf h1 (hp ▸ hin)).elim
        · exact hm
    by_cases hst : ts ∈ oc.thread.prom
    · have := ih hq hti' (oh_step hti hoh hxi he hxo hoc fun h => absurd hm h) (hm ▸ hxi) hst hg'
        (by rw [hm]; exact hlast)
      rw [hm] at this; exact this
    · cases he with
      | quiet _ hp => exact absurd (hp ▸ hin) hst
      | ld tr old vv hrd hwi h0 h1 hk hval hn hw hphi hv hcase =>
        rcases hcase with ⟨-, hp, -⟩ | ⟨ts0, -, hg0, -, hp, -⟩
        · exact absurd (hp ▸ hin) hst
        · refine absurd (hp ▸ (List.mem_erase_of_ne fun e => ?_).mpr hin) hst
          subst e; rw [hg] at hg0; cases hg0; exact hxo hl
      | st vv htk hk hn hw hphi hv hcase =>
        rcases hcase with ⟨-, hp, -⟩ | ⟨ts0, -, hg0, -, hp⟩
        · exact absurd (hp ▸ hin) hst
        · refine absurd (hp ▸ (List.mem_erase_of_ne fun e => ?_).mpr hin) hst
          subst e; rw [hg] at hg0; cases hg0; exact hoc hl.symm
      | rl vv h0 h1 hval hord hn hw hphi hv hcase =>
        rcases hcase with ⟨-, hp, -⟩ | ⟨ts0, -, hg0, -, hm', hp, hc0⟩
        · exact absurd (hp ▸ hin) hst
        · by_cases e : ts = ts0
          · subst e; rw [hg] at hg0; cases hg0
            obtain ⟨tr, v, hrd, hv', -⟩ := hord
            refine ⟨tk p.1, tr, v, hrd, hv', hval, ?_, fun ts' w' a b cc d => ?_⟩
            · obtain ⟨ts1, -, hx⟩ := hti.txn h0; exact ⟨ts1, hx⟩
            · refine Classical.byContradiction fun hne => ?_
              have hlt : ts' < ts := by have := p.2.last_le_of_get?_eq_some a; omega_t
              have hin' := hoh ts' w' a b cc (tk p.1) d (.inl ⟨h0, rfl⟩)
              have hin'' : ts' ∈ oc.thread.prom := hp ▸ (List.mem_erase_of_ne hne).mpr hin'
              have := coh_lt_of_certOkN ⟨_, _, hrest, hq⟩ hin'' (by rw [hm']; exact a)
              rw [b] at this; omega_t
          · exact absurd (hp ▸ (List.mem_erase_of_ne e).mpr hin) hst

end Kraken.Promising.Live.TicketLoopCert
