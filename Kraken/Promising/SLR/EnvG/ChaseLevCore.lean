/-
**The memory-level core of a Chase–Lev proof on `EnvG`.**
ISA-neutral; additive (new file, uses `DekkerCore`'s `NoWriteIn`/`SBFact`
through their statements only).

The `.kl` programs are `Examples/LockFree/{AArch64,X64}/chaselev2{,_nofence}.kl`
(Lê, Pop, Cohen, Zappa Nardelli, PPoPP 2013). Owner's take:
`b := bottom - 1; store bottom b; fence full; t := load top; if t < b then
return buf[b]`, without a CAS. Thief's steal: `t := load acq top; fence full;
b := load acq bottom; if t < b then x := buf[t]; CAS top t → t+1`. The
explorer finds the duplicate outcome (take and steal both get the same slot)
exactly when the owner's fence is removed.

## The argument, as for Dekker (`DekkerCore.lean`)

There is no SC-fence logic. `EnvG` exposes the machine's own timestamps, and
the memory's timestamp order is total.
- **Owner.** After `store bottom b; fence .sy; load top`, the owner has
  Dekker's `SBFact`: its message `bottom := b` is at `tw`, and its read of
  `top` (value `t_o`, at `tr_o`) has no write to `top` in `(tr_o, tw]`
  (`Dekker.sbFact_of_steps`). On AArch64 `vcgen` sees the exact `dmb ish`
  step (`MachineWP.dmb_shared_spec`, priority 50); on x64 it sees `mfence`.
- **Thief.** The thief's fact is read→read, not store→load (`StealFact`). Its
  acquire load of `top` reads the message at `tr1` (value `t`) and raises
  `vrNew` to `tr1`. Its later read of `bottom` (value `b'`, at `tr2`) then has
  no write to `bottom` in `(tr2, tr1]` (`stealFact_of_load`). The thief's own
  CAS write plays no part.
- **Key lemma** (`chaseLev_key`). Assume (i) `top`'s values do not decrease
  along timestamps (`TopMono`: every write to `top` is a CAS `t → t+1`) and
  (ii) no `bottom` message at or above the owner's decrement holds more than
  `b` (`BotLate`: the owner's take on its `t < b` path is its last write to
  `bottom`). Then a CAS-free take of slot `b` (`t_o < b`) and a non-empty
  steal of index `t` (`t < b'`) are at different slots. Either the thief's
  `top` message is at or below the owner's read, so `t ≤ t_o < b`, or it lies
  above the owner's window, so the thief read `bottom` at or above the
  decrement and `b' ≤ b`.
- **Slot visibility** (`slotRead_of_pub`). The thief may read `bottom` from the
  owner's *plain* decrement store, so it gets no plan resource for the slot.
  The slot's value instead follows from a memory fact. If each slot `i` is
  written once, with value `x` (`SlotOnce`), below every `bottom` message
  greater than `i` (`SlotPub`), then an acquire read of `bottom > i` followed
  by a read of slot `i` returns `x`.

So the whole-program proof can be Dekker-style: an empty plan, every store
pure, each thread's invariant carrying these memory facts at its snapshot
(`*.snapLe`, `*.of_envRel`), and a final argument on the final memory. That
final argument discharges `TopMono`, `BotLate`, `SlotPub` and `SlotOnce` from
the exact write histories (`Dekker.flagHist_of_erase`-style). 

## Contents

- `StealFact`, `.prefix`, `.snapLe`, `.of_envRel`, `stealFact_of_load`,
  `acqRead_of_load`.
- `TopMono`, `BotLate`, `chaseLev_key`, `chaseLev_key_facts`.
- `SlotPub`, `SlotOnce`, `slotRead_of_window`, `slotRead_of_pub`.
-/
import Kraken.Promising.SLR.EnvG.DekkerCore

namespace Kraken.Promising.SLR.EnvG.ChaseLev

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.EnvG.Dekker

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `DekkerCore`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

/-! ## Reads of the memory -/

/-- A read at a non-zero timestamp is of a message to that location. -/
theorem get?_of_read? {m : Memory} {l : Loc} {t : Time} {v : Val} (h : m.read? l t = some v) (h0 : t ≠ 0) :
    ∃ w, m.get? t = some w ∧ w.loc = l ∧ w.val = v := by
  unfold Memory.read? at h
  simp only [h0, ↓reduceIte] at h
  split at h
  · next w hw =>
    split at h
    · next hl => exact ⟨w, hw, beq_iff_eq.mp hl, Option.some.inj h⟩
    · cases h
  · cases h

/-- A readable timestamp is at most the memory's last one. -/
theorem le_last_of_read? {m : Memory} {l : Loc} {t : Time} {v : Val} (h : m.read? l t = some v) :
    t ≤ m.last := by
  by_cases h0 : t = 0
  · omega_t
  · obtain ⟨w, hw, -⟩ := get?_of_read? h h0
    exact Memory.last_le_of_get?_eq_some m hw

/-! ## The thief's fact -/

/-- **The steal fact** at memory `m`: the thief read `top = t` at `tr1`, and
then `bottom = b` at `tr2` with no write to `bottom` in `(tr2, tr1]`. -/
structure StealFact (m : Memory) (top bot : Loc) (t b : Val) (tr1 tr2 : Time) : Prop where
  readTop : m.read? top tr1 = some t
  readBot : m.read? bot tr2 = some b
  window : NoWriteIn m bot tr2 tr1

variable {m m' : Memory} {top bot : Loc} {t b : Val} {tr1 tr2 : Time}

/-- `StealFact` is stable under memory extension. -/
theorem StealFact.prefix (h : StealFact m top bot t b tr1 tr2) (hi : m'.init = m.init)
    (hp : m.msgs.toList <+: m'.msgs.toList) : StealFact m' top bot t b tr1 tr2 where
  readTop := read?_of_prefix hi hp h.readTop
  readBot := read?_of_prefix hi hp h.readBot
  window := h.window.prefix hp (le_last_of_read? h.readTop)

/-- `StealFact` is stable under re-anchoring (any thread's `SnapLe`). -/
theorem StealFact.snapLe {tid' : Nat} {c c' : Config I} (hs : SnapLe tid' c c')
    (h : StealFact c.mem top bot t b tr1 tr2) : StealFact c'.mem top bot t b tr1 tr2 :=
  h.prefix hs.init hs.msgs

/-- `StealFact` of the env's snapshot holds of the actual configuration
(`EnvRel.snap`), in particular of a final one. -/
theorem StealFact.of_envRel {tid' : Nat} {pl : Plan} {σ : State I} {c : Config I} {th : Thread I}
    {r : Res} {g : Ghost} {cl : Prop} (hr : EnvRel tid' pl σ c th r g cl)
    (h : StealFact σ.snap.mem top bot t b tr1 tr2) : StealFact c.mem top bot t b tr1 tr2 :=
  h.snapLe hr.snap

/-- **An acquire load's read and view**: an acquire-kind load of `l` reading
`v`, not from the thread's own forwarding buffer, reads a message at some
`tr` of its snapshot and raises `vrNew` to at least `tr`. A forwarded read
(the thief reading its own CAS write) is not covered here; there the thief's
full fence gives the bound instead (`Dekker.vwOld_le_vrNew_of_fence`, with the
CAS's `tw ≤ vwOld` from `RmwFacts`). -/
theorem acqRead_of_load {A : Arch} {tid : Nat} {σ σ' : State I} {kl : LoadKind} {l : Loc} {v : Val}
    (hl : LoadFacts A tid σ σ' kl l v) (hacq : (A.loadKind kl).isAcquire = true)
    (hnf : ∀ tr, σ'.snap.mem.read? l tr = some v → ¬ Fwded σ.vs l tr) :
    ∃ tr, σ'.snap.mem.read? l tr = some v ∧ tr ≤ σ'.vs.vrNew := by
  obtain ⟨-, -, -, tr, hread, hlv, -⟩ := hl
  exact ⟨tr, hread.val, (hlv.acq hacq (hnf tr hread.val)).1⟩

/-- **The steal fact from the load of `bottom`**: before it, the snapshot
reads `top = t` at `tr1` and `vrNew` is at least `tr1` (after the thief's
acquire load of `top`, `acqRead_of_load`, and any steps that keep both). The
load's `LoadFacts` give the `StealFact` at its snapshot. -/
theorem stealFact_of_load {A : Arch} {tid : Nat} {σ σ' : State I} {kl : LoadKind}
    (hread1 : σ.snap.mem.read? top tr1 = some t) (hvr : tr1 ≤ σ.vs.vrNew)
    (hl : LoadFacts A tid σ σ' kl bot b) : ∃ tr2, StealFact σ'.snap.mem top bot t b tr1 tr2 := by
  obtain ⟨hanc, -, -, tr2, hread, -⟩ := hl
  have hb : σ.vs.vrNew ≤ readBound A σ.vs kl bot := by
    unfold readBound
    omega_t
  exact ⟨tr2, read?_of_prefix hanc.snap.init hanc.snap.msgs hread1, hread.val,
    (noWriteIn_of_writeIn hread.window).mono (Nat.le_trans hvr hb)⟩

/-! ## The key lemma -/

/-- `top`'s values do not decrease along timestamps (the initial value at
`0` included). In `chaselev2.kl` every write to `top` is a successful CAS
`t → t+1`, atomic with its read. -/
def TopMono (m : Memory) (top : Loc) : Prop :=
  ∀ t1 t2 v1 v2, t1 ≤ t2 → m.read? top t1 = some v1 → m.read? top t2 = some v2 → v1.toNat ≤ v2.toNat

/-- No message of `bottom` at or above `tw` holds more than `b`. This holds
when the owner's write at `tw` is its last write to `bottom` (a take on its
`t < b` path) and no other thread writes `bottom`. -/
def BotLate (m : Memory) (bot : Loc) (tw : Time) (b : Val) : Prop :=
  ∀ ts v, tw ≤ ts → m.read? bot ts = some v → v.toNat ≤ b.toNat

/-- **The Chase–Lev key lemma, memory level.** The owner's take wrote
`bottom := b` at `tw` and read `top = t_o` at `tr_o` with no `top` write in
`(tr_o, tw]` (its `SBFact`). A steal read `top = t` and then `bottom = b'`
(its `StealFact`). Under `TopMono` and `BotLate`, a CAS-free take
(`t_o < b`) and a non-empty steal (`t < b'`) are not of the same slot.
`bottom ≠ top` is not needed: the owner's message at `tw` is to `bottom`. -/
theorem chaseLev_key {tid0 : Nat} {b t_o b' : Val} {tw tr_o : Time}
    (ho : SBFact m tid0 bot b top t_o tw tr_o) (hs : StealFact m top bot t b' tr1 tr2)
    (hmono : TopMono m top) (hlate : BotLate m bot tw b)
    (htake : t_o.toNat < b.toNat) (hsteal : t.toNat < b'.toNat) : t.toNat ≠ b.toNat := by
  intro heq
  by_cases h1 : tr1 ≤ tr_o
  · have := hmono tr1 tr_o t t_o h1 hs.readTop ho.read
    omega
  · have h10 : tr1 ≠ 0 := by omega_t
    obtain ⟨w, hw, hwl, -⟩ := get?_of_read? hs.readTop h10
    -- the thief's `top` message is not in the owner's window `(tr_o, tw]`
    have htw : tw < tr1 := by
      refine Nat.not_le.mp fun hle => ?_
      exact ho.window tr1 w (Nat.lt_of_not_le h1) hle hw hwl
    -- so the owner's decrement is not in the thief's window `(tr2, tr1]`
    have h2 : tw ≤ tr2 := by
      refine Nat.not_lt.mp fun hlt => ?_
      exact hs.window tw ⟨bot, b, tid0⟩ hlt (Nat.le_of_lt htw) ho.own rfl
    have := hlate tr2 b' h2 hs.readBot
    omega

/-- `chaseLev_key` on the actual configuration, from the two threads' facts
at their snapshots (`SBFact.of_envRel`, `StealFact.of_envRel`): the form a
final argument (`hB` of `ThreadRuleRX.ofSafelyEnvG(X)`) uses. -/
theorem chaseLev_key_facts {tid0 tid1 : Nat} {pl0 pl1 : Plan} {σ0 σ1 : State I} {c : Config I}
    {th0 th1 : Thread I} {r0 r1 : Res} {g0 g1 : Ghost} {cl0 cl1 : Prop}
    {b t_o b' : Val} {tw tr_o : Time}
    (hr0 : EnvRel tid0 pl0 σ0 c th0 r0 g0 cl0) (hr1 : EnvRel tid1 pl1 σ1 c th1 r1 g1 cl1)
    (ho : SBFact σ0.snap.mem tid0 bot b top t_o tw tr_o) (hs : StealFact σ1.snap.mem top bot t b' tr1 tr2)
    (hmono : TopMono c.mem top) (hlate : BotLate c.mem bot tw b)
    (htake : t_o.toNat < b.toNat) (hsteal : t.toNat < b'.toNat) : t.toNat ≠ b.toNat :=
  chaseLev_key (ho.of_envRel hr0) (hs.of_envRel hr1) hmono hlate htake hsteal

/-! ## Slot visibility without a plan resource -/

/-- **Slot `s` is published by `bottom`**: every message of `bottom` whose
value exceeds the slot's index `i` lies above a message of `s` by the owner
`tid0`. -/
def SlotPub (m : Memory) (bot s : Loc) (i : Nat) (tid0 : Nat) : Prop :=
  ∀ ts v, m.read? bot ts = some v → i < v.toNat → ∃ tw x, tw < ts ∧ m.get? tw = some ⟨s, x, tid0⟩

/-- **Slot `s` holds `x` once written**: every message of `s` has value `x`. -/
def SlotOnce (m : Memory) (s : Loc) (x : Val) : Prop :=
  ∀ ts w, m.get? ts = some w → w.loc = s → w.val = x

/-- **A windowed read of a written slot**: a read of `s` at `trs` with no
write to `s` in `(trs, hi]`, where some message of `s` lies at `tw ≤ hi`,
reads at or above `tw`; under `SlotOnce` it returns `x`. -/
theorem slotRead_of_window {s : Loc} {x v : Val} {trs tw hi : Time} {w : Msg}
    (hread : m.read? s trs = some v) (hwin : NoWriteIn m s trs hi) (hw : m.get? tw = some w)
    (hwl : w.loc = s) (htw : tw ≤ hi) (hx : SlotOnce m s x) : v = x := by
  have hle : tw ≤ trs := Nat.not_lt.mp fun hlt => hwin tw w hlt htw hw hwl
  have h0 : trs ≠ 0 := by
    intro h0
    have : tw ≠ 0 := by
      intro e
      rw [e] at hw
      simp [Memory.get?] at hw
    omega_t
  obtain ⟨w', hw', hwl', hv⟩ := get?_of_read? hread h0
  rw [← hv]
  exact hx trs w' hw' hwl'

/-- **Slot visibility from `bottom`**: the thief read `bottom = b'` at `tr2`,
and its later read of slot `s` (index `i < b'`) has no write to `s` in
`(trs, hi]` with `tr2 ≤ hi`. This holds for any load after an acquire load of
`bottom` (`acqRead_of_load`: `tr2 ≤ vrNew ≤ readBound`). Under `SlotPub` and
`SlotOnce` the slot read returns `x`, with no plan resource and whichever
`bottom` message the thief read: a release (a push's `STLR`) or the owner's
plain decrement. -/
theorem slotRead_of_pub {s : Loc} {i tid0 : Nat} {b' x v : Val} {trs hi : Time}
    (hbot : m.read? bot tr2 = some b') (hi_ : i < b'.toNat) (hread : m.read? s trs = some v)
    (hwin : NoWriteIn m s trs hi) (h2 : tr2 ≤ hi) (hpub : SlotPub m bot s i tid0) (hx : SlotOnce m s x) :
    v = x := by
  obtain ⟨tw, y, htw, hw⟩ := hpub tr2 b' hbot hi_
  exact slotRead_of_window hread hwin hw rfl (Nat.le_trans (Nat.le_of_lt htw) h2) hx

end Kraken.Promising.SLR.EnvG.ChaseLev
