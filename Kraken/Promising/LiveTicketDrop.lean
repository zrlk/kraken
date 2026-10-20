/-
**Stage 3: the ticket-lock worker drops at
most one promise per instruction** (`DropBounded Arch.armv8 1`), so weak
fairness gives weak fairness for instruction steps on every ticket-lock trace,
promises included (`weakFairInstr_ticket`).

- `writeSuccs_prom_len`: a write (fulfil or "promise now") removes at most
  one outstanding promise, whatever the promise set. Fulfilling erases one
  timestamp; "promise now" appends the fresh timestamp and erases it again.
- `spec_store_len`/`spec_rmw_len`: the same for a whole `STR`/`STLR` and
  `LDADDA` step, with arbitrary promises (the `LiveTicketStep` shapes
  `spec_store`/`spec_rmw` assume none).
- `SInv`: the promise-agnostic part of `TInv` (`Static` and a pc in
  `tkPcs`), kept by every instruction step (`step_sinv`), hence along
  `ThreadNP` (`threadNP_sinv`); `dropBounded_of_sinv`.
- `trace_sinv`: `SInv` at every thread of every index of a stuttering trace
  from a start configuration (instruction and promise steps).
-/
import Kraken.Promising.LiveTicketInv
import Kraken.Promising.LiveWfInstr

namespace Kraken.Promising.Live.TicketDrop

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live
open Kraken.Promising.Live.TicketTrees Kraken.Promising.Live.TicketStep Kraken.Promising.Live.TicketInv
open Kraken.Promising.SLR.EnvG.TicketLock (tkWorker StartState)

/-! ## Writes drop at most one promise -/

section Write

variable {I : ISA} (A : Arch) (tid : Nat) (iv : InstrViews)

/-- **A write removes at most one outstanding promise**, for any promise set. -/
theorem writeSuccs_prom_len {c c' : Ctx} {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val} {tr : Option Time}
    {extra : View} (h : c' ∈ writeSuccs A tid iv c k xcl l v tr extra) : c.prom.length ≤ c'.prom.length + 1 := by
  unfold writeSuccs at h
  rw [List.mem_append, List.mem_filterMap] at h
  rcases h with ⟨t, -, h⟩ | h
  · cases hg : c.mem.get? t with
    | none => simp [hg] at h
    | some w =>
      simp only [hg] at h
      rw [Option.ite_none_right_eq_some] at h
      obtain ⟨-, h⟩ := h
      obtain rfl := Option.some.inj h
      show c.prom.length ≤ (c.prom.erase t).length + 1
      rw [List.length_erase]
      split <;> omega
  · generalize c.mem.append { loc := l, val := v, tid } = ap at h
    obtain ⟨mem', t⟩ := ap
    simp only at h
    rw [List.mem_ite_nil_right, List.mem_singleton] at h
    obtain ⟨-, rfl⟩ := h
    show c.prom.length ≤ ((c.prom ++ [t]).erase t).length + 1
    rw [List.length_erase]
    simp

theorem run_store_len {σ : Type} {c c' : Ctx} {k : StoreKind} {l : Loc} {v : Val} {s st : σ}
    (h : .ok (st, c') ∈ runTree A tid iv c (.store k false l v fun _ => .done s)) :
    st = s ∧ c.prom.length ≤ c'.prom.length + 1 := by
  simp only [runTree, Bool.false_and, Bool.false_eq_true, ↓reduceIte, List.append_nil,
    List.mem_flatMap] at h
  obtain ⟨c1, h1, h⟩ := h
  obtain ⟨rfl, rfl⟩ := run_done A tid iv h
  exact ⟨rfl, writeSuccs_prom_len A tid _ h1⟩

theorem run_rmw_len {σ : Type} (hA : A.rmwFence = false) {c c' : Ctx} {k : RmwKind} {l : Loc}
    {g : Val → Val} {f : Val → σ} {st : σ}
    (h : .ok (st, c') ∈ runTree A tid iv c (.rmw k false l (fun old => some (g old)) fun v => .done (f v))) :
    ∃ old, st = f old ∧ c.prom.length ≤ c'.prom.length + 1 := by
  simp only [runTree, hA, Bool.false_eq_true, ↓reduceIte, List.mem_flatMap, List.mem_singleton,
    Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨tr, old, c1⟩, hx, c2, h2, hst, hc⟩ := h
  obtain ⟨tr', old', hx', -, -, -, -⟩ := (mem_readSuccs A).mp hx
  simp only [Prod.mk.injEq] at hx'
  obtain ⟨rfl, rfl, rfl⟩ := hx'
  have hl := writeSuccs_prom_len A tid iv h2
  rw [readNext_prom] at hl
  subst hc
  refine ⟨_, hst, ?_⟩
  split <;> exact hl

variable {t : Thread I} {mem : Memory} {outs : List (Except String (Outcome I))} {o : Outcome I}

/-- A non-exclusive store, with any promise set: at most one promise dropped. -/
theorem spec_store_len {k : StoreKind} {l : Loc} {v : Val} {s : I.State}
    (hex : I.exec t.st = some (.store k false l v fun _ => .done s)) (hs : stepOne A t tid mem = some outs)
    (ho : .ok o ∈ outs) : o.thread.st = s ∧ t.prom.length ≤ o.thread.prom.length + 1 := by
  obtain ⟨st, c', hr, -, hst, hp, -, -⟩ := stepOne_out A tid hex hs ho
  obtain ⟨rfl, hl⟩ := run_store_len A tid _ hr
  exact ⟨hst, hp ▸ hl⟩

/-- An always-writing RMW, with any promise set: at most one promise dropped. -/
theorem spec_rmw_len (hA : A.rmwFence = false) {k : RmwKind} {l : Loc} {g : Val → Val} {f : Val → I.State}
    (hex : I.exec t.st = some (.rmw k false l (fun old => some (g old)) fun v => .done (f v)))
    (hs : stepOne A t tid mem = some outs) (ho : .ok o ∈ outs) :
    ∃ old, o.thread.st = f old ∧ t.prom.length ≤ o.thread.prom.length + 1 := by
  obtain ⟨st, c', hr, -, hst, hp, -, -⟩ := stepOne_out A tid hex hs ho
  obtain ⟨old, rfl, hl⟩ := run_rmw_len A tid _ hA hr
  exact ⟨old, hst, hp ▸ hl⟩

end Write

/-! ## The promise-agnostic thread invariant -/

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout tkWorker)]

set_option hygiene false in
local notation "pcA" => (layout tkWorker).addrOf

/-- **The promise-agnostic per-thread invariant**: `Static` and a pc in
`tkPcs` (`TInv` without the promise and register facts). -/
structure SInv (x o c : BitVec 64) (s : isa.State) : Prop where
  st : Static x o c s
  pc : ∃ i ∈ tkPcs, s.st.2 = pcA i

local macro "sinv" hS:ident hst:ident "," j:num : term =>
  `(⟨by rw [$hst:ident]; exact ($hS).goto _ _ rfl rfl rfl rfl, $j, by decide, by rw [$hst:ident] <;> rfl⟩)

/-- **One instruction step keeps `SInv` and drops at most one promise**, for
any promise set and memory. -/
theorem step_sinv {x o c : BitVec 64} {t : Thread isa} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Outcome isa))} {oc : Outcome isa} (h : SInv x o c t.st)
    (hs : stepOne Arch.armv8 t tid mem = some outs) (ho : .ok oc ∈ outs) :
    SInv x o c oc.thread.st ∧ t.prom.length ≤ oc.thread.prom.length + 1 := by
  obtain ⟨hS, i, hi, hpc⟩ := h
  simp only [tkPcs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨-, hst, hp, -⟩ := spec_done _ _ (exec_mov _ (hS.at (by decide) (by decide) hpc)) hs ho
    exact ⟨sinv hS hst, 2, by rw [hp]; omega⟩
  · obtain ⟨old, hst, hl⟩ := spec_rmw_len _ _ rfl (exec_ldadda _ (hS.at (by decide) (by decide) hpc) hS.x0 hS.dx) hs ho
    exact ⟨sinv hS hst, 4, hl⟩
  · obtain ⟨ts, v, hst, -, -, -, hp, -⟩ :=
      spec_load _ _ (exec_ldar _ (hS.at (by decide) (by decide) hpc) hS.x1 hS.dO) hs ho
    exact ⟨sinv hS hst, 5, by rw [hp]; omega⟩
  · obtain ⟨sf, hex, -⟩ := exec_cmp _ (hS.at (by decide) (by decide) hpc)
    obtain ⟨-, hst, hp, -⟩ := spec_done _ _ hex hs ho
    exact ⟨sinv hS hst, 6, by rw [hp]; omega⟩
  · obtain ⟨-, hst, hp, -⟩ := spec_done _ _ (exec_bne _ (hS.at (by decide) (by decide) hpc)) hs ho
    refine ⟨?_, by rw [hp]; omega⟩
    by_cases hz : t.st.st.1.status.z = true
    · rw [ite_eq_left hz] at hst; exact sinv hS hst, 7
    · rw [ite_eq_right hz] at hst; exact sinv hS hst, 4
  · obtain ⟨ts, v, hst, -, -, -, hp, -⟩ :=
      spec_load _ _ (exec_ldr_c _ (hS.at (by decide) (by decide) hpc) hS.x2 hS.dc) hs ho
    exact ⟨sinv hS hst, 8, by rw [hp]; omega⟩
  · obtain ⟨-, hst, hp, -⟩ := spec_done _ _ (exec_add5 _ (hS.at (by decide) (by decide) hpc)) hs ho
    exact ⟨sinv hS hst, 9, by rw [hp]; omega⟩
  · obtain ⟨hst, hl⟩ := spec_store_len _ _ (exec_str_c _ (hS.at (by decide) (by decide) hpc) hS.x2 hS.dc) hs ho
    exact ⟨sinv hS hst, 10, hl⟩
  · obtain ⟨-, hst, hp, -⟩ := spec_done _ _ (exec_add4 _ (hS.at (by decide) (by decide) hpc)) hs ho
    exact ⟨sinv hS hst, 11, by rw [hp]; omega⟩
  · obtain ⟨hst, hl⟩ := spec_store_len _ _ (exec_stlr _ (hS.at (by decide) (by decide) hpc) hS.x1 hS.dO) hs ho
    exact ⟨sinv hS hst, 12, hl⟩
  · obtain ⟨-, hst, hp, -⟩ := spec_done _ _ (exec_b_done _ (hS.at (by decide) (by decide) hpc)) hs ho
    exact ⟨sinv hS hst, 14, by rw [hp]; omega⟩
  · rw [stepOne_end hS hpc] at hs; cases hs

/-- `SInv` along a run of the thread alone. -/
theorem threadNP_sinv {x o c : BitVec 64} {tid : Nat} {p q : Thread isa × Memory}
    (h : ThreadNP Arch.armv8 tid p q) (hp : SInv x o c p.1.st) : SInv x o c q.1.st :=
  ThreadNP.stateInv (SInv x o c) (fun h hs ho => (step_sinv h hs ho).1) h hp

/-- **A worker satisfying `SInv` drops at most one promise per instruction.** -/
theorem dropBounded_of_sinv {x o c : BitVec 64} {tid : Nat} {t : Thread isa} (h : SInv x o c t.st) :
    DropBounded Arch.armv8 1 tid t :=
  dropBounded_of_stateInv (SInv x o c) (fun h hs ho => step_sinv h hs ho) h

/-! ## Along a trace -/

/-- **`SInv` at every thread of every index** of a stuttering trace from a
start configuration, promise steps included. -/
theorem trace_sinv {fuel N : Nat} {x o c : BitVec 64} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : Ticket.TkStart N x o c states initMem) (tr : TraceS Arch.armv8 fuel isa)
    (h0 : tr.cfg 0 = Config.init states initMem) :
    ∀ i (tid : Nat) t, (tr.cfg i).threads[tid]? = some t → SInv x o c t.st
  | 0, tid, t, ht => by
    rw [h0] at ht
    obtain ⟨hT, -, j, hj, hpc, -⟩ := (inv_init hs).thr tid t ht
    exact ⟨hT, j, hj, hpc⟩
  | i + 1, tid, t, ht => by
    have ih := trace_sinv hs tr h0 i
    rcases tr.step i with hm | ⟨-, he⟩
    · obtain ⟨j, -, hst⟩ := stepBy_of_mem_succs hm
      rcases hst with ⟨u, outs, oc, hu, hso, ho, he⟩ | ⟨u, p, hu, -, he⟩
      · rw [he] at ht
        rcases wt_get hu ht with ⟨-, rfl⟩ | ⟨-, ht⟩
        · exact (step_sinv (ih j u hu) hso ho).1
        · exact ih tid t ht
      · rw [he] at ht
        rcases wt_get hu ht with ⟨-, rfl⟩ | ⟨-, ht⟩
        · exact ih j u hu
        · exact ih tid t ht
    · rw [he] at ht; exact ih tid t ht

/-- **Weak fairness gives weak fairness for instruction steps on every
ticket-lock trace**, promises included: every thread drops at most one
promise per instruction (`DropBounded Arch.armv8 1`). -/
theorem weakFairInstr_ticket {fuel N : Nat} {x o c : BitVec 64} {states : List isa.State}
    {initMem : List (Loc × Val)} (hs : Ticket.TkStart N x o c states initMem) (tr : TraceS Arch.armv8 fuel isa)
    (h0 : tr.cfg 0 = Config.init states initMem) (hf : WeakFair Arch.armv8 fuel tr.cfg) :
    WeakFairInstr Arch.armv8 fuel tr.cfg :=
  weakFairInstr_of_weakFair (B := 1) tr (fun i tid t ht => dropBounded_of_sinv (trace_sinv hs tr h0 i tid t ht)) hf

end Kraken.Promising.Live.TicketDrop

#print axioms Kraken.Promising.Live.TicketDrop.weakFairInstr_ticket
