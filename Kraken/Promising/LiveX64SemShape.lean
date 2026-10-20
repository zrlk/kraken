/-
**Stage 3: a fencing RMW with outstanding promises,
and its replay against a larger memory** (ISA-neutral; `A.rmwFence = true`,
`Arch.tso`: x86's `lock`-prefixed instructions).

`LiveSemShape.spec_rmw_p`/`replay_rmw` (and `LiveTicketDrop.spec_rmw_len`)
assume `A.rmwFence = false`. Under `rmwFence`, `runTree` wraps the RMW in
`fence .sy` before its read and after its write; the fences change `vrNew`
and `vwNew` only (not memory, promises, coherence views or `vwOld`), so the
same facts hold (the three pairs differ only in the fences):

- `spec_rmw_p_tso`: an always-writing RMW, with any promise set: an atomic
  read, then an append or the fulfilment of an outstanding promise.
- `replay_rmw_tso`: an outcome that does not append replays against any
  larger memory, for a thread whose views are at most the smaller memory's
  `|M|`.
- `spec_rmw_len_tso`: at most one promise dropped.
-/
import Kraken.Promising.LiveSemShape
import Kraken.Promising.LiveTsoRmw

namespace Kraken.Promising.Live.X64SemShape

set_option linter.unusedSectionVars false

open Kraken.Promising Kraken.Promising.Live Kraken.Promising.Live.TicketStep Kraken.Promising.Live.SemShape
open Kraken.Promising.Live.TsoRmw

variable {I : ISA}

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

theorem fence_vwOld (c : Ctx) (k : FenceKind) : (fenceStep c k).views.vwOld = c.views.vwOld := by
  cases k <;> rfl

theorem fence_eq_mem (c : Ctx) (mem : Memory) (k : FenceKind) :
    fenceStep { c with mem := mem } k = { fenceStep c k with mem := mem } := by
  cases k <;> rfl

private theorem rmwPost_eq' (b : Bool) (c : Ctx) (l : Loc) :
    let c' := if b then ({ c with rmwWrote := true, views := { c.views with
        vrNew := max c.views.vrNew (c.views.getCoh l), vwNew := max c.views.vwNew (c.views.getCoh l) } } : Ctx)
      else { c with rmwWrote := true }
    c'.mem = c.mem ∧ c'.prom = c.prom ∧ c'.views.vwOld = c.views.vwOld := by
  cases b <;> exact ⟨rfl, rfl, rfl⟩

section Spec

variable (A : Arch) (tid : Nat) {t : Thread I} {mem : Memory} {outs : List (Except String (Outcome I))}
  {o : Outcome I}

/-- **A fencing always-writing RMW, with any promise set**: an atomic read,
then an append or a fulfilment (`SemShape.spec_rmw_p` under `rmwFence`). -/
theorem spec_rmw_p_tso (hA : A.rmwFence = true) {k : RmwKind} {l : Loc} {g : Val → Val} {f : Val → I.State}
    (hex : I.exec t.st = some (.rmw k false l (fun old => some (g old)) fun v => .done (f v)))
    (hs : stepOne A t tid mem = some outs) (ho : .ok o ∈ outs) :
    ∃ tr old, o.thread.st = f old ∧ mem.read? l tr = some old ∧
    ((o.mem = (mem.append { loc := l, val := g old, tid }).1 ∧
      o.thread.prom = (t.prom ++ [mem.last + 1]).erase (mem.last + 1) ∧
      ((A.storeKind (A.rmwKind k).storeKind == .nt) = false → mem.last + 1 ≤ o.thread.views.vwOld) ∧
      mem.atomic l tid tr (mem.last + 1) = true) ∨
    (∃ ts ∈ t.prom, mem.get? ts = some { loc := l, val := g old, tid } ∧ t.views.getCoh l < ts ∧
      o.mem = mem ∧ o.thread.prom = t.prom.erase ts ∧ t.views.vwOld ≤ o.thread.views.vwOld ∧
      tr < ts ∧ mem.atomic l tid tr ts = true)) := by
  obtain ⟨c', hr, hm, hp, hv⟩ := stepOne_outV A tid hex hs ho
  simp only [runTree, hA, ↓reduceIte, List.mem_flatMap, List.mem_singleton,
    Except.ok.injEq, Prod.mk.injEq] at hr
  obtain ⟨⟨tr, old, c1⟩, hx, c2, h2, hst, hc⟩ := hr
  have hd := readSuccs_dord A _ hx
  obtain ⟨tr', old', hx', -, hrd, -, -⟩ := (mem_readSuccs A).mp hx
  simp only [Prod.mk.injEq] at hx'
  obtain ⟨rfl, rfl, rfl⟩ := hx'
  rw [fence_mem] at hrd
  obtain ⟨q1, q2, q3⟩ := rmwPost_eq' (A.rmwKind k == RmwKind.acqRel && !false) c2 l
  subst hc
  refine ⟨_, _, hst, hrd, ?_⟩
  have hcoh0 : (fenceStep (ctx0 tid t mem) .sy).views.getCoh l = t.views.getCoh l := fence_getCoh _ _ _
  have hvw0 : (fenceStep (ctx0 tid t mem) .sy).views.vwOld = t.views.vwOld := fence_vwOld _ _
  rcases SemShape.mem_writeSuccs A tid _ h2 with ⟨e1, e2, e3, -, e5⟩ | ⟨ts, hts, e1, e2, -, e4, e5, e6, e7⟩
  · obtain ⟨-, ha⟩ := e5 _ rfl
    exact .inl ⟨hm.trans ((fence_mem _ _).trans (q1.trans e1)), hp.trans ((fence_prom _ _).trans (q2.trans e2)),
      fun hk => by rw [hv, fence_vwOld, q3]; exact e3 hk, ha⟩
  · obtain ⟨a1, a2⟩ := e7 _ rfl
    refine .inr ⟨ts, hts, e1, ?_, hm.trans ((fence_mem _ _).trans (q1.trans e4)),
      hp.trans ((fence_prom _ _).trans (q2.trans e5)), by rw [hv, fence_vwOld, q3, ← hvw0]; exact e6, a1, a2⟩
    rw [← hcoh0]; exact Nat.lt_of_le_of_lt (hd.coh l) e2

/-- A fencing always-writing RMW, with any promise set: at most one promise
dropped (`TicketDrop.spec_rmw_len` under `rmwFence`). -/
theorem spec_rmw_len_tso (hA : A.rmwFence = true) {k : RmwKind} {l : Loc} {g : Val → Val} {f : Val → I.State}
    (hex : I.exec t.st = some (.rmw k false l (fun old => some (g old)) fun v => .done (f v)))
    (hs : stepOne A t tid mem = some outs) (ho : .ok o ∈ outs) :
    ∃ old, o.thread.st = f old ∧ t.prom.length ≤ o.thread.prom.length + 1 := by
  obtain ⟨tr, old, hst, -, h⟩ := spec_rmw_p_tso A tid hA hex hs ho
  refine ⟨old, hst, ?_⟩
  rcases h with ⟨-, hp, -⟩ | ⟨ts, -, -, -, -, hp, -⟩ <;> rw [hp, List.length_erase] <;> split <;> (try simp) <;> omega

end Spec

/-! ## Replay against a larger memory -/

section Replay

variable (A : Arch) (tid : Nat) {t : Thread I} {mem0 mem : Memory} {outs : List (Except String (Outcome I))}
  {o : Outcome I}

/-- **A fencing RMW outcome that does not append replays against a larger
memory** (`SemShape.replay_rmw` under `rmwFence`). -/
theorem replay_rmw_tso (hp : mem0.Prefix mem) (hb : t.Bnd mem0.last) (hs : stepOne A t tid mem0 = some outs)
    (ho : .ok o ∈ outs) (hm : o.mem = mem0) (hA : A.rmwFence = true) {k : RmwKind} {l : Loc} {g : Val → Val}
    {f : Val → I.State}
    (hex : I.exec t.st = some (.rmw k false l (fun old => some (g old)) fun v => .done (f v))) :
    ∃ outs' o', stepOne A t tid mem = some outs' ∧ .ok o' ∈ outs' ∧ o'.thread = o.thread ∧ o'.mem = mem := by
  refine stepOne_replay_of_run A tid hex hs ho hm fun st c0' hr hm' => ?_
  have hiv := instrViews_le hb.regs (I.deps t.st)
  have hcb : (fenceStep (ctx0 tid t mem0) .sy).Bnd :=
    fenceStep_bnd ⟨hb.views, fun _ h => absurd h List.not_mem_nil, Nat.zero_le _⟩ .sy
  have hv := hcb.views.le
  have hbd : ∀ kl, max (readPre A (instrViews t (I.deps t.st)) (fenceStep (ctx0 tid t mem0) .sy) kl)
      ((fenceStep (ctx0 tid t mem0) .sy).views.getCoh l) ≤ (fenceStep (ctx0 tid t mem0) .sy).mem.last := by
    intro kl
    have := hiv.addrR; have := hv.vrNew; have := hv.vRel; have := hv.coh l
    have hfm : (fenceStep (ctx0 tid t mem0) .sy).mem.last = mem0.last := by rw [fence_mem]
    simp only [readPre]; split <;> omega_t
  rw [runTree] at hr
  simp only [hA, ↓reduceIte, List.mem_flatMap] at hr
  obtain ⟨⟨tr, old, c1⟩, hx, c2, h2, h⟩ := hr
  dsimp only at h2 h
  rw [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨hst, hc⟩ := h
  have hp' : (fenceStep (ctx0 tid t mem0) .sy).mem.Prefix mem := by rw [fence_mem]; exact hp
  have hx' := readSuccs_replay A _ hp' hx (hbd _)
  obtain ⟨q1, -, -⟩ := rmwPost_eq' (A.rmwKind k == RmwKind.acqRel && !false) c2 l
  have hc1 : c1.mem = mem0 := by
    obtain ⟨tr', old', hxe, -⟩ := (mem_readSuccs A).mp hx
    simp only [Prod.mk.injEq] at hxe
    obtain ⟨-, -, rfl⟩ := hxe
    rfl
  have hm2 : c2.mem = c1.mem := by
    rw [hc1, ← q1, ← fence_mem _ .sy, ← hc]; exact hm'
  have h2' := writeSuccs_replay A tid _ (hc1 ▸ hp) h2 hm2
  rw [runTree]
  simp only [hA, ↓reduceIte, List.mem_flatMap]
  refine ⟨(tr, old, { c1 with mem := mem }), ?_, { c2 with mem := mem }, h2', ?_⟩
  · have e : fenceStep (ctx0 tid t mem) .sy = { fenceStep (ctx0 tid t mem0) .sy with mem := mem } :=
      fence_eq_mem (ctx0 tid t mem0) mem .sy
    rw [e]; exact hx'
  rw [runTree, List.mem_singleton, hst, hc]
  cases (A.rmwKind k == RmwKind.acqRel && !false) <;> rfl

end Replay

end Kraken.Promising.Live.X64SemShape
