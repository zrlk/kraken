/-
Part 6: **the per-access verification conditions of
`treiber_pp.kl`** on the claim-conditional environment `EnvGC`, AArch64
(`Arch.armv8`). Thread `0` (pusher) on `pushPlan`, thread `1` (popper) on
`popPlan` (`EnvG/TreiberGhost.lean`).

**Table predicates.**
- `GW`: the ghost facts both threads use (release predicates `ghost₀`'s,
  acquire table extending `[predP, predU]`, update id `1` at `top`); monotone
  in `Ghost.Le`.
- Pusher: `Pu0` (start), `Pu` (`push`: the node whole, `n1d`'s maximal write
  `(1, t)` with `t ≤ vwOld`, more than half of `top`), `Pd` (done: more than
  half of `top`, which `hB` turns into the shared postcondition's token
  disjunct).
- Popper: `Pp` (`popper`: the token whole, a share of `top`, acquire id `0`
  of `top`, no forwarding item of `top`, `top`'s initial value `0`), `Pc`
  (after a successful `casal`: either the message read was a pusher message,
  `x2 = n1` and the claimed node `S` is in the resource with its maximal
  write at or below `vrNew`, or it was an other message, which the next
  clean erasure refutes: `other_absurd`).

**VCs.** Pusher: `vc_push_str_d`, `vc_push_load`, `vc_push_str_n`,
`vc_push_cas`. Popper: `vc_pop_load`, `vc_pop_cas`, `vc_pop_ldr`.

**The instance of `EnvG/TreiberVCCommon.lean`** at `I := AArch64.isa`,
`A := Arch.armv8`, `op := casOp64` (`casOp64_casMatch`). Every name keeps its
statement: the ISA-free ones (`read?_of_get?`, `get?_of_read?`,
`initVal_eq`, `GW` and its lemmas, `ghost₀_gw`, the plan lemmas,
`lt_op_left`) are `hoist_alias`es of the `TreiberCommon` ones; the table
predicates are definitions by the `TreiberCommon` ones at `isa`; the lemmas
and VCs stated at `isa`/`casOp64` are re-proved from the generic ones.
-/
import Kraken.Promising.SLR.EnvG.TreiberGhost
import Kraken.Promising.SLR.EnvG.TreiberVCCommon
import Kraken.Promising.SLR.EnvG.Alias
import Kraken.Promising.SLR.EnvG.RmwGhostVCGen
import Kraken.Promising.SLR.EnvG.Simp
import Kraken.Promising.SLR.EnvG.Seen
import Kraken.Promising.SLR.SpinAcquire
import Kraken.Promising.SLR.SpinClaim
import Kraken.Promising.SLR.StoreHelpers

namespace Kraken.Promising.SLR.EnvG.Treiber

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.SpinCommon

/-! ## The environments -/

/-- The pusher's environment (thread `0`). -/
noncomputable abbrev EP (P : Params) : SharedEnv := EnvGC isa Arch.armv8 0 (pushPlan P)

/-- The popper's environment (thread `1`). -/
noncomputable abbrev EQ (P : Params) : SharedEnv := EnvGC isa Arch.armv8 1 (popPlan P)

/-- The 64-bit compare-and-swap of `casal Xs, Xt, [Xn]` (`Xs = x`, `Xt = y`). -/
abbrev casOp64 (x y : BitVec 64) : Val → Option Val := rmwOpBits 64 fun o => if (o == x) = true then some y else none

theorem casOp64_some {x y : BitVec 64} {o n : Val} (h : casOp64 x y o = some n) :
    BitVec.setWidth 64 o = x ∧ n = BitVec.setWidth 128 y := by
  simp only [rmwOpBits, Option.map_eq_some_iff] at h
  obtain ⟨a, ha, rfl⟩ := h
  split at ha
  · next h0 => exact ⟨by simpa using h0, by cases ha; rfl⟩
  · cases ha

theorem casOp64_none {x y : BitVec 64} {o : Val} (h : casOp64 x y o = none) : BitVec.setWidth 64 o ≠ x := by
  intro h0
  simp [rmwOpBits, h0] at h

theorem casOp64_casMatch (x y : BitVec 64) : TreiberCommon.CasMatch (casOp64 x y) x y :=
  ⟨fun _ _ h => casOp64_some h, fun _ h => casOp64_none h⟩

/-! ## Memory and step helpers -/

hoist_alias [Kraken.Promising.SLR.EnvG.TreiberCommon.read?_of_get? ↦ Kraken.Promising.SLR.EnvG.Treiber.read?_of_get?,
  Kraken.Promising.SLR.EnvG.TreiberCommon.get?_of_read? ↦ Kraken.Promising.SLR.EnvG.Treiber.get?_of_read?,
  Kraken.Promising.SLR.EnvG.TreiberCommon.initVal_eq ↦ Kraken.Promising.SLR.EnvG.Treiber.initVal_eq]

/-- A message of the snapshot is a message of every admissible anchor. -/
theorem get?_of_anchor {tid : Nat} {σ : State isa} {c : Config isa} {g : Ghost} (h : AnchorOk tid σ c g)
    {ts : Time} {w : Msg} (hw : σ.snap.mem.get? ts = some w) : c.mem.get? ts = some w :=
  TreiberCommon.get?_of_anchor h hw

/-- Where a write lands: the old messages stay, the write is at `tw`. -/
theorem WriteSnap.get?_old {tid : Nat} {c c' : Config isa} {l : Loc} {v : Val} {tw : Time}
    (h : WriteSnap tid c c' l v tw) {ts : Time} {w : Msg} (hw : c.mem.get? ts = some w) : c'.mem.get? ts = some w :=
  TreiberCommon.WriteSnap.get?_old h hw

theorem WriteSnap.get?_new {tid : Nat} {c c' : Config isa} {l : Loc} {v : Val} {tw : Time}
    (h : WriteSnap tid c c' l v tw) : c'.mem.get? tw = some ⟨l, v, tid⟩ :=
  TreiberCommon.WriteSnap.get?_new h

theorem WriteSnap.init {tid : Nat} {c c' : Config isa} {l : Loc} {v : Val} {tw : Time}
    (h : WriteSnap tid c c' l v tw) : c'.mem.init = c.mem.init :=
  TreiberCommon.WriteSnap.init h

/-- A failed RMW of `EnvGC` leaves the forwarding items alone (`EnvGC`'s copy
of `envG_rmw_fail_getFwd`). -/
theorem envGC_rmw_fail_getFwd {A : Arch} {tid : Nat} {pl : Plan} {σ σ' : State isa} {k : RmwKind}
    {addr : BitVec 64} {n : Nat} {op : Val → Option Val} {old : Val}
    (h : (EnvGC isa A tid pl).step (.rmw k addr n op) σ old σ') (hop : op old = none)
    (l : Loc) : σ'.vs.getFwd l = σ.vs.getFwd l :=
  TreiberCommon.envGC_rmw_fail_getFwd h hop l

/-! ## The ghost facts -/

/-! `GW` (the ghost facts both threads rely on: release predicates
`ghost₀`'s, acquire table extending `[predP, predU]`, update id `1` at
`top`), its lemmas and `ghost₀_gw` are the `TreiberCommon` ones. -/

hoist_alias [Kraken.Promising.SLR.EnvG.TreiberCommon.GW ↦ Kraken.Promising.SLR.EnvG.Treiber.GW,
  Kraken.Promising.SLR.EnvG.TreiberCommon.GW.mono ↦ Kraken.Promising.SLR.EnvG.Treiber.GW.mono,
  Kraken.Promising.SLR.EnvG.TreiberCommon.GW.rel_top ↦ Kraken.Promising.SLR.EnvG.Treiber.GW.rel_top,
  Kraken.Promising.SLR.EnvG.TreiberCommon.GW.rel_ne ↦ Kraken.Promising.SLR.EnvG.Treiber.GW.rel_ne,
  Kraken.Promising.SLR.EnvG.TreiberCommon.GW.acqPred_zero ↦ Kraken.Promising.SLR.EnvG.Treiber.GW.acqPred_zero,
  Kraken.Promising.SLR.EnvG.TreiberCommon.GW.acqPred_one ↦ Kraken.Promising.SLR.EnvG.Treiber.GW.acqPred_one,
  Kraken.Promising.SLR.EnvG.TreiberCommon.ghost₀_gw ↦ Kraken.Promising.SLR.EnvG.Treiber.ghost₀_gw]

/-! ## The popper's refutation of an other message -/

/-- An acquire id held at least once by a thread is held once in the total. -/
theorem total_acq_of_ge {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config isa} (E : Erase rF g T c) {i : Nat}
    (hi : i < c.threads.size) {x : Loc} {ι : PredId} (h : 1 ≤ (rF i).acq x ι) : (total rF g c).acq x ι = 1 :=
  TreiberCommon.total_acq_of_ge E hi h

/-- **Two other messages refute a clean erasure**: the popper (thread `1`,
holding the acquire id `0` of `top`) sees a slot of id `0` at each, and each
holds the token whole. -/
theorem other_absurd {P : Params} {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config isa} {r : Res}
    (E : Erase (setRes rF 1 r) g T c) (hn : 1 < c.threads.size) (hW : GW P g) (hacq : 1 ≤ r.acq P.top 0)
    {tr tw : Time} {w : Msg} {new : Val} (hne : tr ≠ tw) (hw : c.mem.get? tr = some w) (hl : w.loc = P.top)
    (ht : w.tid ≠ 0) (hw' : c.mem.get? tw = some ⟨P.top, new, 1⟩) : False :=
  TreiberCommon.other_absurd E hn hW hacq hne hw hl ht hw'

/-! ## The popper -/

/-- **The popper in its loop** (`popper`): `TreiberCommon.Pp` at `isa`. -/
def Pp (P : Params) (σ : State isa) : Prop := TreiberCommon.Pp P σ

/-- **The popper after a successful `casal`** that compared `x2`: a pusher
message was read (`x2 = n1`, the claimed node `S`) or an other message
(refuted by the next clean erasure); `TreiberCommon.Pc` at `isa`. -/
def Pc (P : Params) (x2 : BitVec 64) (σ : State isa) : Prop := TreiberCommon.Pc P x2 σ

hoist_alias [Kraken.Promising.SLR.EnvG.TreiberCommon.popPlan_after_acq ↦
    Kraken.Promising.SLR.EnvG.Treiber.popPlan_after_acq]

/-- **VC of a popper load** (`ldar x2, [x0]`, `ldr x4, [x2, #8]` at any
address): `Pp` is kept. -/
theorem vc_pop_load {P : Params} (σ : State isa) (h : Pp P σ) {k : LoadKind} {xcl : Bool} {a : BitVec 64} {n : Nat} :
    ∀ v (σ' : State isa), (EQ P).step (.load k xcl a n) σ v σ' → Pp P σ' :=
  TreiberCommon.vc_pop_load σ h

/-- **VC `casal x3, x4, [x0]`** of the popper (`x3 = x2 ≠ 0`): permitted (a
share of `top`, its plan's release of the token, `relTop` at the popper's
own message), and every outcome fails (`Pp` kept) or succeeds (`Pc`). -/
theorem vc_pop_cas {P : Params} (hL : TLocs P) (σ : State isa) (h : Pp P σ) (x2 x4 : BitVec 64) (hx2 : x2 ≠ 0) :
    (EQ P).ok (.rmw .acqRel P.top.addr P.top.bytes (casOp64 x2 x4)) σ ∧
      ∀ old (σ' : State isa), (EQ P).step (.rmw .acqRel P.top.addr P.top.bytes (casOp64 x2 x4)) σ old σ' →
        (BitVec.setWidth 64 old ≠ x2 ∧ Pp P σ') ∨ (BitVec.setWidth 64 old = x2 ∧ Pc P x2 σ') :=
  TreiberCommon.vc_pop_cas hL σ h x2 x4 hx2 (casOp64_casMatch x2 x4)

/-- **VC `ldr w11, [x2]`** of the popper after a successful `casal` (`x2`
the address): under the clean flag of the load, `x2 = n1` and the value read
is the node's data `1` (an other message is refuted by `other_absurd`; a
pusher message's node gives `n1d`'s maximal write `(1, t)`, `t ≤ vrNew`, and
`read_max` reads it). -/
theorem vc_pop_ldr {P : Params} (hd : P.n1d = ⟨BitVec.setWidth 64 P.n1, 4⟩) (σ : State isa) (x2 : BitVec 64)
    (h : Pc P x2 σ) :
    ∀ v (σ' : State isa), (EQ P).step (.load .plain false x2 4) σ v σ' →
      (σ'.cl → BitVec.setWidth 64 P.n1 = x2 ∧ BitVec.setWidth 32 v = 1) :=
  TreiberCommon.vc_pop_ldr hd σ x2 h

/-! ## The pusher -/

/-- **The pusher at its start** (`pusher`): the node whole at its initial
messages, more than half of `top`; `TreiberCommon.Pu0` at `isa`. -/
def Pu0 (P : Params) (σ : State isa) : Prop := TreiberCommon.Pu0 P σ

/-- **The pusher in its loop** (`push`): the node whole, `n1d`'s maximal
write `(1, t)` at or below `vwOld`, more than half of `top`;
`TreiberCommon.Pu` at `isa`. -/
def Pu (P : Params) (σ : State isa) : Prop := TreiberCommon.Pu P σ

/-- **The pusher done**: more than half of `top`; `TreiberCommon.Pd` at
`isa`. -/
def Pd (P : Params) (σ : State isa) : Prop := TreiberCommon.Pd P σ

hoist_alias [Kraken.Promising.SLR.EnvG.TreiberCommon.pushPlan_after_ne ↦
    Kraken.Promising.SLR.EnvG.Treiber.pushPlan_after_ne,
  Kraken.Promising.SLR.EnvG.TreiberCommon.pushPlan_after_q_top ↦ Kraken.Promising.SLR.EnvG.Treiber.pushPlan_after_q_top,
  Kraken.Promising.SLR.EnvG.TreiberCommon.lt_op_left ↦ Kraken.Promising.SLR.EnvG.Treiber.lt_op_left]

/-- **VC `str w9, [x1]`** (the node's data, `w9 = 1`): permitted (pure, the
node whole), and the write `(1, tw)` is `n1d`'s maximal, `tw ≤ vwOld`. -/
theorem vc_push_str_d {P : Params} (hL : TLocs P) (σ : State isa) (h : Pu0 P σ) (v : Val) (hv : v = 1#128) :
    (EP P).ok (.store .plain false P.n1d.addr P.n1d.bytes v) σ ∧
      ∀ b (σ' : State isa), (EP P).step (.store .plain false P.n1d.addr P.n1d.bytes v) σ b σ' → Pu P σ' :=
  TreiberCommon.vc_push_str_d hL (by decide) σ h v hv

theorem Pu.fence {P : Params} {σ σ' : State isa} (h : Pu P σ) (hf : FenceLe σ σ') : Pu P σ' :=
  TreiberCommon.Pu.fence h hf

theorem Pu0.fence {P : Params} {σ σ' : State isa} (h : Pu0 P σ) (hf : FenceLe σ σ') : Pu0 P σ' :=
  TreiberCommon.Pu0.fence h hf

theorem Pd.fence {P : Params} {σ σ' : State isa} (h : Pd P σ) (hf : FenceLe σ σ') : Pd P σ' :=
  TreiberCommon.Pd.fence h hf

theorem Pp.fence {P : Params} {σ σ' : State isa} (h : Pp P σ) (hf : FenceLe σ σ') : Pp P σ' :=
  TreiberCommon.Pp.fence h hf

theorem Pc.fence {P : Params} {x2 : BitVec 64} {σ σ' : State isa} (h : Pc P x2 σ) (hf : FenceLe σ σ') :
    Pc P x2 σ' :=
  TreiberCommon.Pc.fence h hf

/-- **VC of a pusher load** (`ldar x2, [x0]`): `Pu` is kept. -/
theorem vc_push_load {P : Params} (σ : State isa) (h : Pu P σ) {k : LoadKind} {xcl : Bool} {a : BitVec 64} {n : Nat} :
    ∀ v (σ' : State isa), (EP P).step (.load k xcl a n) σ v σ' → Pu P σ' :=
  TreiberCommon.vc_push_load σ h

/-- **VC `str x2, [x1, #8]`** (the node's link, any value): permitted (pure,
the node whole), `Pu` kept. -/
theorem vc_push_str_n {P : Params} (hL : TLocs P) (σ : State isa) (h : Pu P σ) (v : Val) :
    (EP P).ok (.store .plain false P.n1n.addr P.n1n.bytes v) σ ∧
      ∀ b (σ' : State isa), (EP P).step (.store .plain false P.n1n.addr P.n1n.bytes v) σ b σ' → Pu P σ' :=
  TreiberCommon.vc_push_str_n hL σ h v

/-- **VC `casal x3, x1, [x0]`** of the pusher (`x3 = x2`, `x1` the node's
address `n1`): permitted (a share of `top`; the plan's release of the node,
whose `relTop` holds at the pusher's message: `predP` by the value `n1`,
`predU` by the node and `t ≤ vwOld < tw`), and every outcome fails (`Pu`
kept) or succeeds (`Pd`). -/
theorem vc_push_cas {P : Params} (hL : TLocs P) (σ : State isa) (h : Pu P σ) (x2 x1 : BitVec 64)
    (hx1 : BitVec.setWidth 128 x1 = P.n1) :
    (EP P).ok (.rmw .acqRel P.top.addr P.top.bytes (casOp64 x2 x1)) σ ∧
      ∀ old (σ' : State isa), (EP P).step (.rmw .acqRel P.top.addr P.top.bytes (casOp64 x2 x1)) σ old σ' →
        (BitVec.setWidth 64 old ≠ x2 ∧ Pu P σ') ∨ (BitVec.setWidth 64 old = x2 ∧ Pd P σ') :=
  TreiberCommon.vc_push_cas hL σ h x2 x1 hx1 (casOp64_casMatch x2 x1)

end Kraken.Promising.SLR.EnvG.Treiber
