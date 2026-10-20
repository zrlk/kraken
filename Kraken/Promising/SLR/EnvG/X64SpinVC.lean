/-
**The x64 xchg spinlock on `EnvG`: the table predicates and the per-access
verification conditions**, for the worker of
`spinlock2.kl` (`spinWorkerG`, `EnvG/X64SpinVCGen.lean`) under `Arch.tso`,
against `EnvG`'s Out/Facts interface. The x64 counterpart of
`EnvG/CasVC.lean` (an AArch64 file, so its ISA-neutral predicates are
re-stated here, adapted). The ISA-neutral part (`LkLe`, `GoodC`, `Acq`, `H1`–`H3`,
`QEnd`, their lemmas and the counter VCs' bodies) lives in `EnvG/LockVC.lean`,
shared with the AArch64 `swpl` lock; the names here are aliases and
instances.

The specification is the SWP lock's, unchanged (`SpinCommon`: `Sys`, `World`,
`Fresh`; `Spinlock`: `Pool`, `Good`, `Bad`, `lockPred`); the plan is
`xlockPlan` (`EnvG/X64SpinRelease.lean`).

**What differs from the CAS lock.**
- *A failed `xchg` writes `1`*: it claims the update slots of the message it
  read, which carry an unknown resource (`lockPred` is trivial at a non-zero
  low word). The table therefore never asks for an exact counter share or an
  exact write set: `Fr` keeps only lower bounds (`Fresh`); the exact counter
  share `1` and the counter's write set are derived from validity under the
  clean flag; the release gives exactly a share `1` of the counter
  (`xlockPlan`).
- *Write set of the lock* (`LkLe`): without a surplus of the lock, every
  non-zero write in the thread's write set of `Lk` is at or below its
  coherence view of `Lk` (the own `xchg` writes; an acquired part with a
  positive lock share makes a surplus). Monotone along every step.
- *Forwarding* (`LkFwd`): the forwarding item of `Lk` (if any) is exclusive
  (the own `xchg`'s), so the `xchg` acquire raises `vrNew`/`vwNew` to the
  message read even when it is forwarded (`rmw_factsX`; `RmwFacts` states the
  acquire bound only for an unforwarded read).

**Table predicates**: `Fr` (at `worker`), `H1` (after a successful `xchg`),
`H2 x5` (after the counter load), `H3 x5` (after the counter store), `QEnd`.

**VCs**: `vc_ld_spin`, `vc_xchg`, `vc_ld_c`, `vc_st_c`, `vc_rel`.

Phase-1 limits apply (single-access trees, read-side acquire only, release
RMWs never fail: `xchg` is total).
-/
import Kraken.Promising.SLR.EnvG.X64SpinRelease
import Kraken.Promising.SLR.EnvG.X64Link
import Kraken.Promising.SLR.SpinAcquire
import Kraken.Promising.SLR.EnvG.LockVC
import Kraken.Promising.SLR.EnvG.Alias

namespace Kraken.Promising.X64.EnvG.Spin

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG
open Kraken.Promising.SLR.Spinlock Kraken.Promising.SLR.SpinCommon Kraken.Promising.SLR.EnvG.X64Spin

/-! ## The environment -/

/-- The bare environment of thread `tid` (the `vcgen` proof restricts it to
the layout `[(l, 4), (c, 4)]`). -/
noncomputable abbrev EG (P : Sys) (tid : Nat) : SharedEnv := Kraken.Promising.SLR.EnvG isa Arch.tso tid (xlockPlan P tid)

/-- The `xchgl %eax, (Lk)` operation with `eax = 1`. -/
abbrev xchgOp : Val → Option Val := rmwOp128 .W32 fun _ => some 1#32

theorem xchgOp_eq (old : Val) : xchgOp old = some 1#128 := by
  simp [xchgOp, rmwOp128]

/-! ## An RMW's facts with an exclusive forwarding item -/

/-- **An RMW's facts, x64 lock form**: as `step_rmwFacts`, but the acquire
bound holds whenever the forwarding item of the location is exclusive (not
only for an unforwarded read), and a successful RMW leaves an exclusive
forwarding item. -/
theorem rmw_factsX {A : Arch} {tid : Nat} {pl : Plan} {σ σ' : EStateX} {k : RmwKind} {addr : BitVec 64}
    {n : Nat} {op : Val → Option Val} {old : Val}
    (h : (Kraken.Promising.SLR.EnvG isa A tid pl).step (.rmw k addr n op) σ old σ')
    (hk : (A.loadKind (A.rmwKind k).loadKind).isAcquire = true)
    (hpl : (A.loadKind (A.rmwKind k).loadKind == .plain) = false) (hxo : A.fwdXclOnlyPlain = true)
    (hfw : ∀ f, σ.vs.getFwd ⟨addr, n⟩ = some f → f.xcl = true) :
    ∃ (c : Config isa) (tr : Time), AnchorOk tid σ c σ'.g ∧ c.mem.read? ⟨addr, n⟩ tr = some old ∧
      VLe σ.vs σ'.vs ∧ σ'.cl = σ.cl ∧ tr ≤ σ'.vs.vrNew ∧ tr ≤ σ'.vs.vwNew ∧
      ((op old = none ∧ σ'.r = σ.r) ∨
       (∃ (new : Val) (tw : Time), op old = some new ∧ tw ≤ σ'.vs.getCoh ⟨addr, n⟩ ∧
         (∃ P : Prop, (σ.cl → P) ∧ σ'.r = pl.afterRmw ⟨addr, n⟩ new tr tw σ'.g P σ.r) ∧
         ¬ σ'.g.Claimed (⟨addr, n⟩, tr) ∧ ∀ f, σ'.vs.getFwd ⟨addr, n⟩ = some f → f.xcl = true)) := by
  obtain ⟨-, -, -, -, hvle, -⟩ := step_rmwFacts h
  obtain ⟨c, x, hanc, hx, hold, hcl, -, -, -, hbr⟩ := (h : RmwOut A tid pl σ σ' k ⟨addr, n⟩ op old)
  have hfw' : ∀ f, (fenceOptCtx A (envCtx tid σ.vs c)).views.getFwd ⟨addr, n⟩ = some f → f.xcl = true :=
    fun f hf => hfw f (by rw [fenceOptCtx_getFwd] at hf; exact hf)
  have hacq := readSuccs_acq_le hx hk hpl fun f hf _ => ⟨hfw' f hf, hxo⟩
  have hrd : c.mem.read? ⟨addr, n⟩ x.1 = some old := by
    obtain ⟨t, v', rfl, -, hrd, -, -⟩ := (mem_readSuccs A).mp hx
    obtain ⟨hc0m, -⟩ := fenceOptCtx_memProm A (envCtx tid σ.vs c)
    rw [hc0m] at hrd
    simp only at hold
    rw [← hold]; exact hrd
  have hpost : VLe x.2.2.views σ'.vs := by
    rcases hbr with ⟨-, -, hvs, -⟩ | ⟨new, cx', tw, -, hc, hev, -, -, -, hvs, -⟩
    · rw [hvs]; exact vle_fenceOpt A _
    · rw [hvs]; exact (writeSuccs_at A tid hc hev).2.mono.trans (vle_rmwAfter A k false _ cx')
  refine ⟨c, x.1, hanc, hrd, hvle, hcl, Nat.le_trans hacq.1 hpost.vrNew, Nat.le_trans hacq.2 hpost.vwNew, ?_⟩
  rcases hbr with ⟨hop, -, -, hr⟩ | ⟨new, cx', tw, hop, hc, hev, -, -, -, hvs, hr, hun⟩
  · exact .inl ⟨hop, hr⟩
  · refine .inr ⟨new, tw, hop, ?_, hr, hun, fun f hf => ?_⟩
    · rw [hvs]; exact Nat.le_trans (writeSuccs_at A tid hc hev).2.coh (vle_rmwAfter A k false _ cx' |>.coh _)
    · rw [hvs, rmwAfter_getFwd] at hf
      exact writeSuccs_getFwd_xcl hc f hf

/-! ## The table predicates -/

variable {P : Sys} {tid : Nat}

/-! **The write set of the lock** `LkLe`, the predicates `GoodC`, `Acq` and
their lemmas, `fresh_join` and `LkLe.*`: aliases of the ISA-neutral
originals in `EnvG/LockVC.lean` (moved there verbatim, shared with
`EnvG/SwplLockVC.lean`), with their statements. -/
hoist_alias [Kraken.Promising.SLR.EnvG.LockVC.LkLe ↦ Kraken.Promising.X64.EnvG.Spin.LkLe,
  Kraken.Promising.SLR.EnvG.LockVC.GoodC ↦ Kraken.Promising.X64.EnvG.Spin.GoodC,
  Kraken.Promising.SLR.EnvG.LockVC.Acq ↦ Kraken.Promising.X64.EnvG.Spin.Acq,
  Kraken.Promising.SLR.EnvG.LockVC.Acq.mono ↦ Kraken.Promising.X64.EnvG.Spin.Acq.mono,
  Kraken.Promising.SLR.EnvG.LockVC.Acq.q ↦ Kraken.Promising.X64.EnvG.Spin.Acq.q,
  Kraken.Promising.SLR.EnvG.LockVC.Acq.counter ↦ Kraken.Promising.X64.EnvG.Spin.Acq.counter,
  Kraken.Promising.SLR.EnvG.LockVC.fresh_join ↦ Kraken.Promising.X64.EnvG.Spin.fresh_join,
  Kraken.Promising.SLR.EnvG.LockVC.LkLe.mono ↦ Kraken.Promising.X64.EnvG.Spin.LkLe.mono,
  Kraken.Promising.SLR.EnvG.LockVC.LkLe.join ↦ Kraken.Promising.X64.EnvG.Spin.LkLe.join,
  Kraken.Promising.SLR.EnvG.LockVC.LkLe.addW_ne ↦ Kraken.Promising.X64.EnvG.Spin.LkLe.addW_ne]

/-- The forwarding item of `Lk`, if any, is exclusive. -/
def LkFwd (P : Sys) (vs : Views) : Prop := ∀ f, vs.getFwd P.Lk = some f → f.xcl = true

/-- **Before taking the lock** (`worker`). -/
def Fr (P : Sys) (tid : Nat) (σ : EStateX) : Prop :=
  World P σ.g ∧ Fresh P tid σ.r ∧ LkFwd P σ.vs ∧ LkLe P σ.r σ.vs

/-- **Holding the lock** (after a successful `xchg`; `LockVC.H1`). -/
abbrev H1 (P : Sys) (tid : Nat) (σ : EStateX) : Prop := LockVC.H1 P tid σ

/-- **After the counter load** of `x5` (`LockVC.H2`): under the clean flag,
the resource is valid and the counter value is `|S|` (or the acquired part
was `Bad`). -/
abbrev H2 (P : Sys) (tid : Nat) (x5 : BitVec 32) (σ : EStateX) : Prop := LockVC.H2 P tid x5 σ

/-- **After the counter store** of `x5` at `tw ≤ vwOld` (`LockVC.H3`); under
the clean flag the store is above every earlier counter write. -/
abbrev H3 (P : Sys) (tid : Nat) (x5 : BitVec 32) (σ : EStateX) : Prop := LockVC.H3 P tid x5 σ

/-- **The end** (`LockVC.QEnd`): the world, and under the clean flag the
worker's `Post`. -/
abbrev QEnd (P : Sys) (σ : EStateX) : Prop := LockVC.QEnd P σ

/-! ## The VCs -/

/-- **VC `movl (%rdi), %eax`** (the spin): `Fr` is kept. -/
theorem vc_ld_spin (σ : EStateX) (h : Fr P tid σ) :
    ∀ v (σ' : EStateX), (EG P tid).step (.load .plain false P.Lk.addr P.Lk.bytes) σ v σ' → Fr P tid σ' := by
  intro v σ' hs
  obtain ⟨hanc, hr, -, tr, -, hlv, -⟩ := step_loadFacts hs
  obtain ⟨hW, hf, hfw, hz⟩ := h
  refine ⟨hW.mono hanc.ghost, hr ▸ hf, fun f hf' => hfw f (by rw [hlv.getFwd] at hf'; exact hf'), ?_⟩
  rw [hr]; exact hz.mono (hlv.mono.coh _)

/-- Under `Arch.tso` the `xchg` (`rmw .acqRel`) is an acquire read. -/
theorem tso_acq : (Arch.tso.loadKind (Arch.tso.rmwKind .acqRel).loadKind).isAcquire = true := by decide

theorem tso_notPlain : (Arch.tso.loadKind (Arch.tso.rmwKind .acqRel).loadKind == .plain) = false := by decide

/-- **VC `xchgl %eax, (%rdi)`** (`eax = 1`): permitted (a lock share, a pure
written value `1`, the claim condition: acquire-release), and every outcome
either reads a non-zero low word (`Fr` kept, with the claimed part joined) or
takes the lock (`H1`). -/
theorem vc_xchg (hN0 : 0 < P.N) (σ : EStateX) (h : Fr P tid σ) :
    (EG P tid).ok (.rmw .acqRel P.Lk.addr P.Lk.bytes xchgOp) σ ∧
      ∀ old (σ' : EStateX), (EG P tid).step (.rmw .acqRel P.Lk.addr P.Lk.bytes xchgOp) σ old σ' →
        (BitVec.setWidth 32 old ≠ 0 ∧ Fr P tid σ') ∨ (BitVec.setWidth 32 old = 0 ∧ H1 P tid σ') := by
  obtain ⟨hW, hf, hfw, hz⟩ := h
  refine ⟨⟨?_, fun c g tr old new _ _ hop => ⟨fun _ => .inl rfl, fun _ => ?_, fun hr => ?_⟩⟩, ?_⟩
  · show 0 < (σ.r.wr P.Lk).q
    have := one_div_pos hN0; have := hf.2.2; grind
  · rw [xchgOp_eq] at hop; cases hop
    rw [hW.1]; exact lockPred_pure (by decide)
  · rw [xchgOp_eq] at hop; cases hop
    rw [xlockPlan_rel_one] at hr; cases hr
  intro old σ' hs
  obtain ⟨c, tr, hanc, hrd, hvle, -, hvr, hvw, hbr⟩ := rmw_factsX hs tso_acq tso_notPlain rfl hfw
  rcases hbr with ⟨hop, -⟩ | ⟨new, tw, hop, hcoh, ⟨_, -, hr⟩, hun, hfw'⟩
  · rw [xchgOp_eq] at hop; cases hop
  rw [xchgOp_eq] at hop; cases hop
  have hr' : σ'.r = (σ.r.op (Res.prod ((claimedSlots σ'.g P.Lk tr).map (·.res)))).addW P.Lk (1#128, tw) := by
    rw [hr, Plan.afterRmw, Plan.after, xlockPlan_rel_one]; rfl
  have hz' : LkLe P σ'.r σ'.vs := by rw [hr']; exact LkLe.join hf hz (hvle.coh _) hcoh
  by_cases h0 : BitVec.setWidth 32 old = 0
  · refine .inr ⟨h0, hW.mono hanc.ghost, hz', ?_⟩
    obtain ⟨rF, E'⟩ := hanc.erase
    obtain ⟨R, R', hprod, hgb⟩ := World.lock_claim' (hW.mono hanc.ghost) E' hrd h0 hun
    have hr'' : σ'.r = (σ.r.op (R.op R')).addW P.Lk (1#128, tw) := by rw [hr', hprod]
    rcases hgb with ⟨k, S, ts, hpool, hX, hmax, hk, hts⟩ | hbad
    · exact ⟨S, k, R, σ.r, R', tw, hr'', hf, hpool,
        .inl ⟨ts, hX, hmax, hk, Nat.le_trans hts hvr, Nat.le_trans hts hvw⟩⟩
    · obtain ⟨S, hpool⟩ := hbad.2
      exact ⟨S, 0, R, σ.r, R', tw, hr'', hf, hpool, .inr hbad⟩
  · exact .inl ⟨h0, hW.mono hanc.ghost, by rw [hr']; exact fresh_join hf, hfw', hz'⟩

/-- **VC `movl (%rsi), %ecx`** (the counter): `H1` is kept, and under the
clean flag of the load's anchor the resource is valid and a `Good`
acquisition reads the counter's maximal write `|S|` (`read_max`). -/
theorem vc_ld_c (hLC : P.Lk ≠ P.C) (σ : EStateX) (h : H1 P tid σ) :
    ∀ v (σ' : EStateX), (EG P tid).step (.load .plain false P.C.addr P.C.bytes) σ v σ' →
      H2 P tid (BitVec.setWidth 32 v) σ' :=
  fun _ _ hs => LockVC.vc_ld_cG hLC h (step_loadFacts hs)

/-- **VC `movl %ecx, (%rsi)`** (the counter, plain, pure value): permitted
(at least a full counter share, the counter's predicate pure), and every
outcome adds `(x5, tw)`; under the clean flag above every earlier counter
write. -/
theorem vc_st_c (hLC : P.Lk ≠ P.C) (x5 : BitVec 32) (σ : EStateX) (h : H2 P tid x5 σ) :
    (EG P tid).ok (.store .plain false P.C.addr P.C.bytes (BitVec.setWidth 128 (x5 + 1))) σ ∧
      ∀ b (σ' : EStateX), (EG P tid).step (.store .plain false P.C.addr P.C.bytes (BitVec.setWidth 128 (x5 + 1)))
        σ b σ' → H3 P tid (x5 + 1) σ' :=
  have h' := LockVC.vc_st_cG (by decide) hLC x5 (I := isa) (σ := σ) h
  ⟨h'.1, fun _ σ' hs => h'.2 σ' (step_storeFacts hs)⟩

/-- **VC `movl $0, (%rdi)`** (the lock release, a plain store of `0`, a
release under `Arch.tso`; `xlockPlan`'s split): permitted from `H3`
(`storeOk_xlockRelease`), and every outcome ends in `QEnd`
(`xlockRelease_post`; without a surplus, `LkLe` bounds the own non-zero writes
of `Lk` by the coherence view, below the release). An instance of
`LockVC.vc_relG`. -/
theorem vc_rel (hL : SpinLocs P.N P.Lk P.C P.K P.F) (hN0 : 0 < P.N) (htid : tid < P.N) (hN32 : P.N < 2 ^ 32)
    (x5 : BitVec 32) (σ : EStateX) (h : H3 P tid x5 σ) :
    (EG P tid).ok (.store .plain false P.Lk.addr P.Lk.bytes 0) σ ∧
      ∀ b (σ' : EStateX), (EG P tid).step (.store .plain false P.Lk.addr P.Lk.bytes 0) σ b σ' → QEnd P σ' :=
  have hG := LockVC.vc_relG (A := Arch.tso) (sk := .plain) rfl hL hN0 htid hN32 h
  ⟨hG.1, fun _ _ hs => by
    obtain ⟨_, _, hanc, -, hwb, -, -, ⟨_, hPc, hr⟩, hcl', -⟩ := step_storeFacts hs
    exact hG.2 hanc.ghost hcl' hwb.coh hPc hr⟩

end Kraken.Promising.X64.EnvG.Spin
