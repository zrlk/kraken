/-
**Part 2: the SWP spinlock with a `swpl`
release on `EnvGC` — table predicates and per-access verification
conditions**, for `swplWorker` (`EnvG/SwplLockSmoke.lean`) against `EnvGC`'s
Out/Facts interface.

The specification is the SWP lock's, unchanged (`SpinCommon`: `Sys`, `World`,
`Fresh`; `Spinlock`: `Pool`, `Good`, `Bad`, `lockPred`). The plan is the x64
xchg lock's `xlockPlan` (`EnvG/X64SpinRelease.lean`, ISA-neutral): a write of
`0` to `Lk` is a release giving the pool, a share `1` of the counter and a
share of the lock chosen by the clean knowledge.

**Why the x64 xchg lock is the template, not the CAS lock.** A failed `swpa`
writes `1`, so (like a failed `xchg`) it may claim the update slots of the
message it read, which carry an unknown resource. The table therefore keeps
only lower bounds before the acquisition (`Fresh`), derives the exact counter
share from validity under the clean flag, and the release gives exactly a
share `1` of the counter (`xlockPlan`). The predicates `LkLe`, `GoodC`, `Acq`,
`H1`–`H3`, `QEnd` and the lemmas `Acq.*`, `fresh_join`, `LkLe.*` are shared
with `X64SpinVC.lean` through the ISA-neutral `EnvG/LockVC.lean` (aliases and
instances here), as are the bodies of `vc_ldr_c`/`vc_str_c`.

**What differs from the x64 lock.**
- *Forwarding.* `swpa` is an acquire RMW, not acquire-release, so on `EnvGC`
  it claims only when its read is not forwarded (`ClaimOk`). A forwarded read
  of the lock reads the thread's own last `swpa` write, whose value is `1`:
  `LkFwdM` records that the forwarding item of `Lk` (if any) is a message
  `(Lk, 1, tid)` of the anchor's memory, which only grows (`SnapLe`). So a
  read of a zero low word is never forwarded, and the `swpa` then claims
  (`World.lock_claim'`) and raises `vrNew`/`vwNew` to the message read.
- *Release.* `swpl wzr, w2, [x0]` is a release-only RMW: on `EnvGC` it claims
  nothing (`claimSlotsC_armv8_rel`) and gives from the thread's own resource
  (`RmwOkC`), so its permission is the store release's
  (`storeOk_xlockRelease`, whose release obligation is stated at a write
  bound that the swap's bound implies: `writeBound_tso_of_rel`) and its
  outcome is `xlockRelease_post`.

**Table predicates**: `Fr` (`worker`, `try`, `spin`), `H1` (`cs`), `H2 x5`,
`H3 x5`, `QEnd`. **VCs**: `vc_swpa`, `vc_ldr_spin`, `vc_ldr_c`, `vc_str_c`,
`vc_swpl`.

Phase-1 limits apply (single-access trees, read-side acquire only, an
in-flight release RMW never fails: the swap is total).
-/
import Kraken.Promising.SLR.EnvG.SwplLockSmoke
import Kraken.Promising.SLR.EnvG.LockVC
import Kraken.Promising.SLR.EnvG.Alias
import Kraken.Promising.SLR.EnvG.X64SpinRelease
import Kraken.Promising.SLR.EnvG.RmwGhostVCGen
import Kraken.Promising.SLR.EnvG.Simp
import Kraken.Promising.SLR.SpinAcquire
import Kraken.Promising.SLR.SpinClaim

namespace Kraken.Promising.SLR.EnvG.SwplLock

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.SLR.EnvG
open Kraken.Promising.SLR.Spinlock Kraken.Promising.SLR.SpinCommon Kraken.Promising.SLR.EnvG.X64Spin
open Kraken.Promising.SLR.EnvG.CasSmoke (lockGives lockDelta)

/-! ## The environment -/

/-- The environment of thread `tid`: claim-conditional RMWs, the x64 lock's
plan. -/
noncomputable abbrev E (P : Sys) (tid : Nat) : SharedEnv := EnvGC isa Arch.armv8 tid (xlockPlan P tid)

/-! ## The write of an RMW of `EnvGC`: its message and forwarding item -/

/-- **A successful RMW of `EnvGC` lands its message and forwards it**: the
new snapshot holds the message `(l, new, tid)` at some `tw`, and the
forwarding item of `l` is at `tw`. -/
theorem rmwC_write {A : Arch} {tid : Nat} {pl : Plan} {σ σ' : State isa} {k : RmwKind} {addr : BitVec 64}
    {n : Nat} {op : Val → Option Val} {old new : Val}
    (h : (EnvGC isa A tid pl).step (.rmw k addr n op) σ old σ') (hop : op old = some new) :
    ∃ tw, σ'.snap.mem.get? tw = some ⟨⟨addr, n⟩, new, tid⟩ ∧
      ∃ f, σ'.vs.getFwd ⟨addr, n⟩ = some f ∧ f.time = tw := by
  obtain ⟨c, x, -, -, hold, -, -, -, -, hbr⟩ := (h : RmwOutC A tid pl σ σ' k ⟨addr, n⟩ op old)
  rcases hbr with ⟨hop', -⟩ | ⟨new', cx', tw, hop', hc, hev, -, -, hsnap, hvs, -, -⟩
  · rw [hop] at hop'; cases hop'
  rw [hop] at hop'; cases hop'
  refine ⟨tw, ?_, ?_⟩
  · rw [hsnap]
    show cx'.mem.get? tw = _
    rcases hev.cases with ⟨hm, -, hg⟩ | ⟨hm, rfl⟩
    · rw [hm]; exact hg
    · rw [hm]; exact Memory.get?_append_last _ _
  · rw [hvs, rmwAfter_getFwd]
    exact (writeSuccs_at A tid hc hev).2.fwd

/-- A message of the snapshot is a message of every admissible anchor. -/
theorem get?_of_anchor {tid : Nat} {σ : State isa} {c : Config isa} {g : Ghost} (h : AnchorOk tid σ c g)
    {ts : Time} {w : Msg} (hw : σ.snap.mem.get? ts = some w) : c.mem.get? ts = some w :=
  Memory.get?_of_prefix h.snap.msgs hw

/- `read?_of_get?`: a message is read at its timestamp (alias of
`SLR.read?_of_get?'`, `SLR/ReleaseStore.lean`). -/
hoist_alias [Kraken.Promising.SLR.read?_of_get?' ↦ Kraken.Promising.SLR.EnvG.SwplLock.read?_of_get?]

/-! ## The table predicates -/

variable {P : Sys} {tid : Nat}

/-! **The write set of the lock** (`X64SpinVC.LkLe`), the predicates `GoodC`,
`Acq` and their lemmas, `fresh_join` and `LkLe.*`: aliases of the
ISA-neutral originals in `EnvG/LockVC.lean` (formerly copies of
`X64SpinVC.lean`'s), with their statements. -/
hoist_alias [Kraken.Promising.SLR.EnvG.LockVC.LkLe ↦ Kraken.Promising.SLR.EnvG.SwplLock.LkLe,
  Kraken.Promising.SLR.EnvG.LockVC.GoodC ↦ Kraken.Promising.SLR.EnvG.SwplLock.GoodC,
  Kraken.Promising.SLR.EnvG.LockVC.Acq ↦ Kraken.Promising.SLR.EnvG.SwplLock.Acq,
  Kraken.Promising.SLR.EnvG.LockVC.Acq.mono ↦ Kraken.Promising.SLR.EnvG.SwplLock.Acq.mono,
  Kraken.Promising.SLR.EnvG.LockVC.Acq.q ↦ Kraken.Promising.SLR.EnvG.SwplLock.Acq.q,
  Kraken.Promising.SLR.EnvG.LockVC.Acq.counter ↦ Kraken.Promising.SLR.EnvG.SwplLock.Acq.counter,
  Kraken.Promising.SLR.EnvG.LockVC.fresh_join ↦ Kraken.Promising.SLR.EnvG.SwplLock.fresh_join,
  Kraken.Promising.SLR.EnvG.LockVC.LkLe.mono ↦ Kraken.Promising.SLR.EnvG.SwplLock.LkLe.mono,
  Kraken.Promising.SLR.EnvG.LockVC.LkLe.join ↦ Kraken.Promising.SLR.EnvG.SwplLock.LkLe.join,
  Kraken.Promising.SLR.EnvG.LockVC.LkLe.addW_ne ↦ Kraken.Promising.SLR.EnvG.SwplLock.LkLe.addW_ne]

/-- **The forwarding item of the lock is an own `1`**: if there is one, the
anchor's memory holds the thread's message `(Lk, 1)` at its timestamp. -/
def LkFwdM (P : Sys) (tid : Nat) (σ : State isa) : Prop :=
  ∀ f, σ.vs.getFwd P.Lk = some f → σ.snap.mem.get? f.time = some ⟨P.Lk, 1#128, tid⟩

/-- **Before taking the lock** (`worker`, `try`, `spin`). -/
def Fr (P : Sys) (tid : Nat) (σ : State isa) : Prop :=
  World P σ.g ∧ Fresh P tid σ.r ∧ LkFwdM P tid σ ∧ LkLe P σ.r σ.vs

/-- **Holding the lock** (`cs`; `LockVC.H1`). -/
abbrev H1 (P : Sys) (tid : Nat) (σ : State isa) : Prop := LockVC.H1 P tid σ

/-- **After the counter load** of `x5` (`LockVC.H2`): under the clean flag,
the resource is valid and the counter value is `|S|` (or the acquired part
was `Bad`). -/
abbrev H2 (P : Sys) (tid : Nat) (x5 : BitVec 32) (σ : State isa) : Prop := LockVC.H2 P tid x5 σ

/-- **After the counter store** of `x5` at `tw ≤ vwOld` (`LockVC.H3`); under
the clean flag the store is above every earlier counter write. -/
abbrev H3 (P : Sys) (tid : Nat) (x5 : BitVec 32) (σ : State isa) : Prop := LockVC.H3 P tid x5 σ

/-- **The end** (`LockVC.QEnd`): the world, and under the clean flag the
worker's `Post`. -/
abbrev QEnd (P : Sys) (σ : State isa) : Prop := LockVC.QEnd P σ

/-! ## The VCs -/

/-- **VC `ldr w2, [x0]`** (the spin): `Fr` is kept (the anchor's memory only
grows, the forwarding items are unchanged). -/
theorem vc_ldr_spin (σ : State isa) (h : Fr P tid σ) :
    ∀ v (σ' : State isa), (E P tid).step (.load .plain false P.Lk.addr P.Lk.bytes) σ v σ' → Fr P tid σ' := by
  intro v σ' hs
  obtain ⟨hanc, hr, -, tr, -, hlv, -⟩ := step_loadFacts (pl := xlockPlan P tid) hs
  obtain ⟨hW, hf, hfw, hz⟩ := h
  refine ⟨hW.mono hanc.ghost, hr ▸ hf, fun f hf' => ?_, ?_⟩
  · rw [hlv.getFwd] at hf'
    exact get?_of_anchor hanc (hfw f hf')
  · rw [hr]; exact hz.mono (hlv.mono.coh _)

/-- **VC `swpa w3, w2, [x0]`** (an acquire swap writing `1`; `op` abstracts
the swap's operation): permitted (a lock share, a pure written value `1`), and
every outcome either reads a non-zero low word (`Fr` kept, with the claimed
part, if any, joined) or takes the lock (`H1`): a zero low word is not the
thread's forwarded own `1` (`LkFwdM`), so the swap claims and its acquire read
raises the views to the message. -/
theorem vc_swpa (hN0 : 0 < P.N) (σ : State isa) (h : Fr P tid σ) (op : Val → Option Val)
    (hop : ∀ x, op x = some 1#128) :
    (E P tid).ok (.rmw .acq P.Lk.addr P.Lk.bytes op) σ ∧
      ∀ old (σ' : State isa), (E P tid).step (.rmw .acq P.Lk.addr P.Lk.bytes op) σ old σ' →
        (BitVec.setWidth 32 old ≠ 0 ∧ Fr P tid σ') ∨ (BitVec.setWidth 32 old = 0 ∧ H1 P tid σ') := by
  obtain ⟨hW, hf, hfw, hz⟩ := h
  have hpos : 0 < (σ.r.wr P.Lk).q := by have := one_div_pos hN0; have := hf.2.2; grind
  refine ⟨⟨hpos, fun c g tr old new _ _ hon => ⟨fun _ => ?_, fun hr => ?_⟩⟩, ?_⟩
  · rw [hop] at hon; cases hon
    rw [hW.1]; exact lockPred_pure (by decide)
  · rw [hop] at hon; cases hon
    rw [xlockPlan_rel_one] at hr; cases hr
  intro old σ' hs
  obtain ⟨tw', hmsg, f', hf', hft'⟩ := rmwC_write hs (hop old)
  obtain ⟨c, tr, hanc, hrd, hvle, -, -, -, -, hacq, hbr⟩ := step_rmwFactsC hs
  rcases hbr with ⟨hon, -⟩ | ⟨new, tw, hon, -, -, -, -, hcoh, -, -, ⟨_, -, hr⟩, hun⟩
  · rw [hop] at hon; cases hon
  rw [hop] at hon; cases hon
  have hr' : σ'.r = (σ.r.op (Res.prod ((claimSlotsC Arch.armv8 .acq σ.vs σ'.g P.Lk tr).map (·.res)))).addW P.Lk
      (1#128, tw) := by
    rw [hr, Plan.after, xlockPlan_rel_one]
    exact Res.addW_op _ _ hpos
  have hz' : LkLe P σ'.r σ'.vs := by rw [hr']; exact LkLe.join hf hz (hvle.coh _) hcoh
  by_cases h0 : BitVec.setWidth 32 old = 0
  · -- not forwarded: a forwarded read returns the own `1`
    have hnf : ¬ Fwded σ.vs P.Lk tr := by
      rintro ⟨f, hf1, rfl⟩
      have hv := read?_of_get? (get?_of_anchor hanc (hfw f hf1))
      rw [hrd.val] at hv
      cases hv
      exact absurd h0 (show BitVec.setWidth 32 (1#128 : Val) ≠ 0 by decide)
    have hok : ClaimOk Arch.armv8 .acq σ.vs P.Lk tr := .inr ⟨by decide, hnf⟩
    obtain ⟨hvr, hvw⟩ := hacq (by decide) hnf
    refine .inr ⟨h0, hW.mono hanc.ghost, hz', ?_⟩
    obtain ⟨rF, E'⟩ := hanc.erase
    obtain ⟨R, R', hprod, hgb⟩ := World.lock_claim' (hW.mono hanc.ghost) E' hrd.val h0 hun
    have hr'' : σ'.r = (σ.r.op (R.op R')).addW P.Lk (1#128, tw) := by rw [hr', claimSlotsC_of_ok hok, hprod]
    rcases hgb with ⟨k, S, ts, hpool, hX, hmax, hk, hts⟩ | hbad
    · exact ⟨S, k, R, σ.r, R', tw, hr'', hf, hpool,
        .inl ⟨ts, hX, hmax, hk, Nat.le_trans hts hvr, Nat.le_trans hts hvw⟩⟩
    · obtain ⟨S, hpool⟩ := hbad.2
      exact ⟨S, 0, R, σ.r, R', tw, hr'', hf, hpool, .inr hbad⟩
  · refine .inl ⟨h0, hW.mono hanc.ghost, by rw [hr']; exact fresh_join hf, fun f hf1 => ?_, hz'⟩
    have e : f = f' := Option.some.inj (hf1.symm.trans hf')
    subst e
    rw [hft']; exact hmsg

/-- **VC `ldr w5, [x1]`** (the counter): `H1` is kept, and under the clean
flag of the load's anchor the resource is valid and a `Good` acquisition
reads the counter's maximal write `|S|` (`read_max`). -/
theorem vc_ldr_c (hLC : P.Lk ≠ P.C) (σ : State isa) (h : H1 P tid σ) :
    ∀ v (σ' : State isa), (E P tid).step (.load .plain false P.C.addr P.C.bytes) σ v σ' →
      H2 P tid (BitVec.setWidth 32 v) σ' :=
  fun _ _ hs => LockVC.vc_ld_cG hLC h (step_loadFacts (pl := xlockPlan P tid) hs)

/-- **VC `str w5, [x1]`** (the counter, plain, pure value): permitted (at
least a full counter share, the counter's predicate pure), and every outcome
adds `(x5, tw)`; under the clean flag above every earlier counter write. -/
theorem vc_str_c (hLC : P.Lk ≠ P.C) (x5 : BitVec 32) (σ : State isa) (h : H2 P tid x5 σ) :
    (E P tid).ok (.store .plain false P.C.addr P.C.bytes (BitVec.setWidth 128 (x5 + 1))) σ ∧
      ∀ b (σ' : State isa), (E P tid).step (.store .plain false P.C.addr P.C.bytes (BitVec.setWidth 128 (x5 + 1)))
        σ b σ' → H3 P tid (x5 + 1) σ' :=
  have h' := LockVC.vc_st_cG (by decide) hLC x5 (I := isa) (σ := σ) h
  ⟨h'.1, fun _ σ' hs => h'.2 σ' (step_storeFacts (pl := xlockPlan P tid) hs)⟩

/-- The write bound of an armv8 release RMW is the bound of a `tso` plain
store (both are release stores): `storeOk_xlockRelease`'s release obligation
applies to the swap. -/
theorem writeBound_tso_of_rel {vs : Views} {l : Loc} {tw : Time}
    (h : WriteBound Arch.armv8 vs (Arch.armv8.rmwKind .rel).storeKind l tw) : WriteBound Arch.tso vs .plain l tw :=
  ⟨h.vwNew, h.vCAP, h.coh, fun _ => h.rel (by decide)⟩

/-- **VC `swpl wzr, w2, [x0]`** (the lock release, a release-only swap
writing `0`; `op` abstracts the swap's operation; `xlockPlan`'s split):
permitted from `H3` (the obligation of `storeOk_xlockRelease`, given from the
thread's own resource), and every outcome ends in `QEnd` (the swap claims
nothing: `xlockRelease_post`; without a surplus, `LkLe` bounds the own
non-zero writes of `Lk` by the coherence view, below the release). The
permission and the outcome are `LockVC.vc_relG`'s. -/
theorem vc_swpl (hL : SpinLocs P.N P.Lk P.C P.K P.F) (hN0 : 0 < P.N) (htid : tid < P.N) (hN32 : P.N < 2 ^ 32)
    (x5 : BitVec 32) (σ : State isa) (h : H3 P tid x5 σ) (op : Val → Option Val) (hop : ∀ x, op x = some 0) :
    (E P tid).ok (.rmw .rel P.Lk.addr P.Lk.bytes op) σ ∧
      ∀ old (σ' : State isa), (E P tid).step (.rmw .rel P.Lk.addr P.Lk.bytes op) σ old σ' → QEnd P σ' := by
  have hG := LockVC.vc_relG (A := Arch.tso) (sk := .plain) rfl hL hN0 htid hN32 h
  have hst := hG.1
  obtain ⟨-, hpos, -, hrelOk⟩ := hst
  refine ⟨⟨hpos, fun c g tr old new hanc _ hon => ⟨fun hr0 => ?_, fun _ => ?_⟩⟩, ?_⟩
  · rw [hop] at hon; cases hon
    rw [xlockPlan_rel_zero] at hr0; cases hr0
  · rw [hop] at hon; cases hon
    obtain ⟨-, himp, hgl, hob⟩ := hrelOk (xlockPlan_rel_zero P tid)
    exact ⟨by decide, himp, hgl, fun _ hwb => hob c g hanc (writeBound_tso_of_rel hwb)⟩
  · -- after the release
    intro old σ' hs
    obtain ⟨c, tr, hanc, -, -, hcl', -, -, -, -, hbr⟩ := step_rmwFactsC hs
    rcases hbr with ⟨hon, -⟩ | ⟨new, tw, hon, -, -, -, hwb, -, -, -, ⟨Pc, hPc, hr'⟩, -⟩
    · rw [hop] at hon; cases hon
    rw [hop] at hon; cases hon
    refine hG.2 hanc.ghost hcl' hwb.coh hPc ?_
    rw [hr', claimSlotsC_armv8_rel]
    simp only [List.map_nil, Res.prod_nil, Res.op_unit]

end Kraken.Promising.SLR.EnvG.SwplLock
