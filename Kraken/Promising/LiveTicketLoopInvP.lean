/-
**The repeated-acquire ticket-lock invariant with
promises** (`LInv`, semantic machine, `tkLoopWorker` running `k` rounds).

`next` (`x`) and `owner` (`o`) messages form chains of values `1, …, xc` and
`1, …, M` (`xc`, `M` their final values). Every `owner` message has a `next`
message of its thread with the same value (`oown`). Every `next` message of
value `v + 1` belongs to a thread that holds ticket `v` (`HoldsV`: taken, or
reserved by an outstanding `next` promise), unless an `owner` message of value
`v + 1` exists (`xheld`). `xc` is the sum over threads of the tickets taken and
the outstanding `next` promises (`xsum`), so `xc ≤ N * k` (`fx_le`): the
certification analysis bounds the promises by the `LDADDA`s left
(`cert_cnt`). Each thread keeps `TI`, `OH`, `cnt` and has no dead promise
(`NoDead`).

So an appended `next` message has value `xc + 1` (an atomic read of the last
one: the own messages between would be dead promises, `fresh_last`,
`cert_x`), and an appended `owner` message value `M + 1` (the release of the
holder of `M`: a smaller ticket's own `owner` message would be an outstanding
promise, dead after a fresh `STLR` or a second one for `cert_o`).

- `inv_step`: `LInv` is kept by every semantic step, and `owner` either keeps
  its value and last write or grows by one.
- `inv_init`, `trace_linv`, `trace_o`.
- `holder_nacert'`: F3 without the `hM32` hypothesis (`M ≤ xc ≤ N * k`, and
  the start condition bounds `N * k`); `holder_nacertV`: F3 for a `HoldsV`
  holder.
-/
import Kraken.Promising.LiveTicketLoopCert
import Kraken.Promising.LiveTicketInvP
import Kraken.Promising.LiveTicketPF

namespace Kraken.Promising.Live.TicketLoopInvP

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live Kraken.Promising.Live.Sem
open Kraken.Promising.Live.TicketLoop Kraken.Promising.Live.TicketLoopTrees Kraken.Promising.Live.TicketLoopStatic
open Kraken.Promising.Live.TicketLoopInv Kraken.Promising.Live.TicketLoopHolder Kraken.Promising.Live.TicketLoopCert
open Kraken.Promising.Live.TicketStep Kraken.Promising.Live.SemShape
open Kraken.Promising.Live.TicketInv (wn L4 loc_ne)
open Kraken.Promising.Live.SpinStep (wt_get wt_tid wt_ne)
open Kraken.Promising.Live.Term (tsum tsum_withThread_add tsum_le)

set_option linter.unusedSectionVars false

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout tkLoopWorker)]

set_option hygiene false in
local notation "pcA" => (layout tkLoopWorker).addrOf

/-- The final value of a word (a notation, so that `omega` sees one atom). -/
scoped notation:max "fv " mem:max a:max => BitVec.toNat (Memory.finalVal mem (L4 a))

/-- An `owner` message of value `n`. -/
def OMsg (o : BitVec 64) (mem : Memory) (n : Nat) : Prop :=
  ∃ ts w, mem.get? ts = some w ∧ w.loc = L4 o ∧ w.val.toNat = n

/-- No outstanding promise is at or below the thread's `coh` of its location. -/
def NoDead (t : Thread isa) (mem : Memory) : Prop :=
  ∀ ts ∈ t.prom, ∀ w, mem.get? ts = some w → t.views.getCoh w.loc < ts

/-- The per-thread part of the invariant. -/
structure TS (k : Nat) (x o c : BitVec 64) (i : Nat) (u : Thread isa) (mem : Memory) : Prop where
  ti : TI k x o c i u mem
  oh : OH x o i u mem
  nd : NoDead u mem
  cnt : countXP x u mem ≤ phi u

/-- **The repeated-acquire ticket-lock invariant with promises.** -/
structure LInv (k N : Nat) (x o c : BitVec 64) (cfg : Config isa) : Prop where
  size : cfg.threads.size = N
  Nk32 : N * k + 1 < 2 ^ 32
  hxo : L4 x ≠ L4 o
  hxc : L4 x ≠ L4 c
  hoc : L4 o ≠ L4 c
  bnd : cfg.Bnd
  xv : ∀ ts v, cfg.mem.read? (L4 x) ts = some v → v.toNat ≤ fv cfg.mem x
  ov : ∀ ts v, cfg.mem.read? (L4 o) ts = some v → v.toNat ≤ fv cfg.mem o
  xinj : XInj x cfg.mem
  oinj : XInj o cfg.mem
  xsurj : ∀ k < fv cfg.mem x, ∃ ts w, cfg.mem.get? ts = some w ∧ w.loc = L4 x ∧ w.val.toNat = k + 1
  osurj : ∀ k < fv cfg.mem o, ∃ ts w, cfg.mem.get? ts = some w ∧ w.loc = L4 o ∧ w.val.toNat = k + 1
  oown : ∀ ts w, cfg.mem.get? ts = some w → w.loc = L4 o → ∃ ts', XMsg x w.tid cfg.mem ts' w.val.toNat
  xheld : ∀ ts w, cfg.mem.get? ts = some w → w.loc = L4 x → ∃ v u, w.val.toNat = v + 1 ∧
    cfg.threads[w.tid]? = some u ∧ (OMsg o cfg.mem (v + 1) ∨ HoldsV x w.tid u cfg.mem v)
  xsum : fv cfg.mem x = tsum cfg (fun _ u => taken k u + countXP x u cfg.mem)
  thr : ∀ (i : Nat) u, cfg.threads[i]? = some u → TS k x o c i u cfg.mem

/-! ## Facts -/

theorem read?_of_get? {mem : Memory} {ts : Time} {w : Msg} (hw : mem.get? ts = some w) :
    mem.read? w.loc ts = some w.val := Kraken.Promising.SLR.read?_of_get?' hw

omit layout hv in
/-- The chain facts of one location across a step (`TicketInvP.chain`, whose
statement does not mention the layout, at the layout of `TicketPF`). -/
theorem chain {mem mem' : Memory} {l : Loc} {tid : Nat}
    (hm : mem' = mem ∨ ∃ w : Msg, w.tid = tid ∧ mem' = (mem.append w).1 ∧
      (w.loc = l → w.val.toNat = (mem.finalVal l).toNat + 1))
    (hv : ∀ ts v, mem.read? l ts = some v → v.toNat ≤ (mem.finalVal l).toNat)
    (hinj : ∀ ts1 ts2 w1 w2, mem.get? ts1 = some w1 → mem.get? ts2 = some w2 → w1.loc = l → w2.loc = l →
      w1.val.toNat = w2.val.toNat → ts1 = ts2)
    (hsurj : ∀ k < (mem.finalVal l).toNat, ∃ ts w, mem.get? ts = some w ∧ w.loc = l ∧ w.val.toNat = k + 1) :
    (∀ ts v, mem'.read? l ts = some v → v.toNat ≤ (mem'.finalVal l).toNat) ∧
    (∀ ts1 ts2 w1 w2, mem'.get? ts1 = some w1 → mem'.get? ts2 = some w2 → w1.loc = l → w2.loc = l →
      w1.val.toNat = w2.val.toNat → ts1 = ts2) ∧
    (∀ k < (mem'.finalVal l).toNat, ∃ ts w, mem'.get? ts = some w ∧ w.loc = l ∧ w.val.toNat = k + 1) ∧
    (∀ ts w, mem'.get? ts = some w → w.loc = l → mem.get? ts = some w ∨ w.tid = tid) ∧
    (((mem'.finalVal l).toNat = (mem.finalVal l).toNat ∧ mem'.lastWrite l = mem.lastWrite l) ∨
      (mem'.finalVal l).toNat = (mem.finalVal l).toNat + 1) :=
  @TicketInvP.chain TicketPF.tkLayout TicketPF.tkValid _ _ _ _ hm hv hinj hsurj

/-- **A worker's tickets taken and `LDADDA`s left add up to `k`.** -/
theorem taken_phi {k : Nat} {x o c : BitVec 64} {i : Nat} {u : Thread isa} {mem : Memory}
    (h : TI k x o c i u mem) : taken k u + phi u = k := by
  obtain ⟨-, j, hj, hpc⟩ := h.sinv
  obtain ⟨a1, -, a3⟩ := cnt_at k hj hpc
  have hk7 := h.k7
  by_cases hb : j ∈ tkBusy
  · have := h.x7 j (by revert hb; simp only [tkBusy, List.mem_cons, List.not_mem_nil, or_false]; omega) hpc
    rw [ite_eq_left hb] at a1 a3; omega
  · rw [ite_eq_right hb] at a1 a3; omega

section Facts

variable {k N : Nat} {x o c : BitVec 64} {cfg : Config isa} (h : LInv k N x o c cfg)
include h

theorem LInv.xv' {ts : Time} {w : Msg} (hw : cfg.mem.get? ts = some w) (hl : w.loc = L4 x) :
    w.val.toNat ≤ fv cfg.mem x := h.xv ts w.val (hl ▸ read?_of_get? hw)

theorem LInv.ov' {ts : Time} {w : Msg} (hw : cfg.mem.get? ts = some w) (hl : w.loc = L4 o) :
    w.val.toNat ≤ fv cfg.mem o := h.ov ts w.val (hl ▸ read?_of_get? hw)

/-- **At most `N * k` tickets** (`xsum`, `cert_cnt`, `taken_phi`). -/
theorem LInv.fx_le : fv cfg.mem x ≤ N * k := by
  rw [h.xsum, ← h.size]
  exact tsum_le fun i u hu => by
    have := (h.thr i u hu).cnt; have := taken_phi (h.thr i u hu).ti; omega

/-- `owner` is at most `next`: the last `owner` message has a `next` twin. -/
theorem LInv.fo_le : fv cfg.mem o ≤ fv cfg.mem x := by
  by_cases h0 : fv cfg.mem o = 0
  · omega
  obtain ⟨ts, w, hw, hl, hv⟩ := h.osurj (fv cfg.mem o - 1) (by omega)
  obtain ⟨ts', w', hw', hl', -, hv'⟩ := h.oown ts w hw hl
  have := h.xv' hw' hl'; omega

theorem LInv.fx32 : fv cfg.mem x + 1 < 2 ^ 32 := by have := h.fx_le; have := h.Nk32; omega

end Facts

/-! ## Holding a ticket in a larger memory -/

theorem HoldsV.mono {x : BitVec 64} {i v : Nat} {u : Thread isa} {mem mem' : Memory} (h : HoldsV x i u mem v)
    (hp : mem.Prefix mem') : HoldsV x i u mem' v :=
  h.imp id fun ⟨ts, hts, hx⟩ => ⟨ts, hts, hx.mono hp⟩

theorem HoldsV.back {x : BitVec 64} {i v : Nat} {u : Thread isa} {mem mem' : Memory} (h : HoldsV x i u mem' v)
    (hp : mem.Prefix mem') (hwf : ∀ p ∈ u.prom, p ≤ mem.last) : HoldsV x i u mem v :=
  h.imp id fun ⟨ts, hts, hx⟩ => ⟨ts, hts, hx.back hp (hwf ts hts)⟩

theorem OMsg.mono {o : BitVec 64} {mem mem' : Memory} {n : Nat} (h : OMsg o mem n) (hp : mem.Prefix mem') :
    OMsg o mem' n :=
  let ⟨ts, w, hw, h1⟩ := h; ⟨ts, w, by rw [hp.get? (mem.last_le_of_get?_eq_some hw)]; exact hw, h1⟩

/-- **The per-thread invariant against a larger memory** whose new messages
are not the thread's. -/
theorem TS.mono {k : Nat} {x o c : BitVec 64} {i : Nat} {u : Thread isa} {mem mem' : Memory}
    (h : TS k x o c i u mem) (hp : mem.Prefix mem')
    (hnew : ∀ ts w, mem'.get? ts = some w → mem.last < ts → w.tid ≠ i) : TS k x o c i u mem' := by
  have hwf := h.ti.wf
  refine ⟨h.ti.mono hp hnew, fun ts w hw hlo hid v hv hH => ?_, fun ts hts w hw => ?_, ?_⟩
  · by_cases hl : ts ≤ mem.last
    · rw [hp.get? hl] at hw; exact h.oh ts w hw hlo hid v hv (HoldsV.back hH hp hwf)
    · exact absurd hid (hnew ts w hw (by omega_t))
  · rw [hp.get? (hwf ts hts)] at hw; exact h.nd ts hts w hw
  · rw [countXP_mono hp hwf]; exact h.cnt

/-! ## Memory and ticket facts -/

theorem tk_lt (u : Thread isa) : tk u < 2 ^ 32 := Nat.mod_lt _ (by decide)

theorem fv_app_ne (mem : Memory) (w : Msg) (a : BitVec 64) (h : w.loc ≠ L4 a) :
    fv (mem.append w).1 a = fv mem a := by
  rw [finalVal_append, ite_eq_right h]

theorem fv_app_eq (mem : Memory) (w : Msg) (a : BitVec 64) (h : w.loc = L4 a) :
    fv (mem.append w).1 a = w.val.toNat := by
  rw [finalVal_append, ite_eq_left h]

/-- **A fresh atomic write reads the last message** when the messages between
would be dead outstanding promises (`PCov`, the writer's `coh` past them). -/
theorem fresh_last {mem : Memory} {l : Loc} {tid : Nat} {t t' : Thread isa} {tr : Time} {old : Val}
    (hrd : mem.read? l tr = some old) (hwi : mem.writeIn l tr (t.views.getCoh l) = false)
    (hat : mem.atomic l tid tr (mem.last + 1) = true) (hpcov : PCov tid t mem)
    (hpr : ∀ ts ∈ t.prom, ts ∈ t'.prom)
    (hnd : ∀ ts ∈ t'.prom, ∀ w, mem.get? ts = some w → t'.views.getCoh w.loc < ts)
    (hco : mem.last + 1 ≤ t'.views.getCoh l) : old = mem.finalVal l := by
  refine (read_lastWrite_of_coh mem l (read?_le hrd) hrd ?_ (mem.lastWrite_le l)).2
  cases e : mem.writeIn l tr mem.last with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨ts, w, h1, h2, hw, hl⟩ := (Memory.writeIn_iff _ _ _ _).mp e
    have hid := Memory.atomic_elim hat hrd ts w h1 (by omega_t) hw hl
    by_cases hc : ts ≤ t.views.getCoh l
    · have := (Memory.writeIn_iff _ _ _ _).mpr ⟨ts, w, h1, hc, hw, hl⟩
      rw [hwi] at this; cases this
    · have hin := hpr ts (hpcov ts w hw hid (by rw [hl]; omega_t))
      have := hnd ts hin w hw
      rw [hl] at this; omega_t

/-- `next` messages after appending a message elsewhere stay injective. -/
theorem xinj_app {x : BitVec 64} {mem : Memory} {w : Msg} (h : XInj x mem) (hl : w.loc ≠ L4 x) :
    XInj x (mem.append w).1 := by
  intro ts1 ts2 w1 w2 h1 h2 hl1 hl2 hv
  rcases mem.get?_append_eq_some w h1 with ⟨-, h1⟩ | ⟨-, rfl⟩
  · rcases mem.get?_append_eq_some w h2 with ⟨-, h2⟩ | ⟨-, rfl⟩
    · exact h ts1 ts2 w1 w2 h1 h2 hl1 hl2 hv
    · exact absurd hl2 hl
  · exact absurd hl1 hl

theorem countXP_prom {x : BitVec 64} {t : Thread isa} {mem : Memory} (w : Msg) (hwf : ∀ p ∈ t.prom, p ≤ mem.last) :
    countXP x (promThread t mem w) (mem.append w).1 = countXP x t mem + (if w.loc = L4 x then 1 else 0) := by
  unfold countXP
  show List.countP _ (t.prom ++ [(mem.append w).2]) = _
  rw [List.countP_append, List.countP_congr fun ts h => by rw [(Memory.Prefix.append mem w).get? (hwf ts h)]]
  rw [Memory.append_time, List.countP_singleton, Memory.get?_append_last]
  by_cases h : w.loc = L4 x <;> simp [h]

/-! ## Preservation -/

section Pres

variable {k N : Nat} {x o c : BitVec 64} {cfg : Config isa} {tid : Nat} {t : Thread isa}
  (h : LInv k N x o c cfg) (ht : cfg.threads[tid]? = some t)
include h ht

/-- **The invariant after a step of `tid`**, from the facts about `tid`. -/
theorem build {t' : Thread isa} {mem' : Memory}
    (hpre : cfg.mem.Prefix mem') (hb : (cfg.withThread tid t' mem').Bnd)
    (hm : mem' = cfg.mem ∨ ∃ w : Msg, w.tid = tid ∧ mem' = (cfg.mem.append w).1 ∧
      (w.loc = L4 x → w.val.toNat = fv cfg.mem x + 1) ∧ (w.loc = L4 o → w.val.toNat = fv cfg.mem o + 1))
    (hT : TS k x o c tid t' mem')
    (hsum : taken k t' + countXP x t' mem' + fv cfg.mem x = taken k t + countXP x t cfg.mem + fv mem' x)
    (hxt : ∀ ts w, mem'.get? ts = some w → w.loc = L4 x → w.tid = tid →
      ∃ v, w.val.toNat = v + 1 ∧ (OMsg o mem' (v + 1) ∨ HoldsV x tid t' mem' v))
    (hot : ∀ ts w, mem'.get? ts = some w → w.loc = L4 o → w.tid = tid → ∃ ts', XMsg x tid mem' ts' w.val.toNat) :
    LInv k N x o c (cfg.withThread tid t' mem') ∧
      ((fv mem' o = fv cfg.mem o ∧ mem'.lastWrite (L4 o) = cfg.mem.lastWrite (L4 o)) ∨
        fv mem' o = fv cfg.mem o + 1) := by
  obtain ⟨x1, x2, x3, x4, -⟩ := chain (l := L4 x) (tid := tid)
    (hm.imp_right fun ⟨w, a, b, d, _⟩ => ⟨w, a, b, d⟩) h.xv h.xinj h.xsurj
  obtain ⟨o1, o2, o3, o4, o5⟩ := chain (l := L4 o) (tid := tid)
    (hm.imp_right fun ⟨w, a, b, _, e⟩ => ⟨w, a, b, e⟩) h.ov h.oinj h.osurj
  have hnew : ∀ ts w, mem'.get? ts = some w → cfg.mem.last < ts → w.tid = tid := fun ts w hw hlt => by
    rcases hm with rfl | ⟨w0, hwt, rfl, -⟩
    · exact absurd (cfg.mem.last_le_of_get?_eq_some hw) (by omega_t)
    · rcases cfg.mem.get?_append_eq_some w0 hw with ⟨hl, -⟩ | ⟨-, rfl⟩
      · exact absurd hl (by omega_t)
      · exact hwt
  have hTo : ∀ (i : Nat) u, i ≠ tid → cfg.threads[i]? = some u → TS k x o c i u mem' := fun i u hi hu =>
    (h.thr i u hu).mono hpre fun ts w hw hlt e => hi (e ▸ hnew ts w hw hlt)
  have hsum' : tsum (cfg.withThread tid t' mem') (fun _ u => taken k u + countXP x u mem') +
      (taken k t + countXP x t cfg.mem) = tsum cfg (fun _ u => taken k u + countXP x u cfg.mem) +
      (taken k t' + countXP x t' mem') :=
    tsum_withThread_add (F := fun _ u => taken k u + countXP x u cfg.mem)
      (F' := fun _ u => taken k u + countXP x u mem') ht fun i u hi hu => by
        rw [countXP_mono hpre (h.thr i u hu).ti.wf]
  refine ⟨⟨by simp [Config.withThread, h.size], h.Nk32, h.hxo, h.hxc, h.hoc, hb, x1, o1, x2, o2, x3, o3,
    fun ts w hw hl => ?_, fun ts w hw hl => ?_, by
      have e : (cfg.withThread tid t' mem').mem = mem' := rfl
      rw [e]; have := h.xsum; omega,
    fun i u hu => ?_⟩, o5⟩
  · by_cases e : w.tid = tid
    · rw [e]; exact hot ts w hw hl e
    · rcases o4 ts w hw hl with hw0 | e'
      · obtain ⟨ts', hx⟩ := h.oown ts w hw0 hl; exact ⟨ts', hx.mono hpre⟩
      · exact absurd e' e
  · by_cases e : w.tid = tid
    · obtain ⟨v, hv, hh⟩ := hxt ts w hw hl e
      exact ⟨v, t', hv, by rw [e]; exact wt_tid ht, by rw [e]; exact hh⟩
    · rcases x4 ts w hw hl with hw0 | e'
      · obtain ⟨v, u, hv, hu, hh⟩ := h.xheld ts w hw0 hl
        exact ⟨v, u, hv, by rw [wt_ne ht e]; exact hu, hh.imp (fun a => OMsg.mono a hpre) (fun a => HoldsV.mono a hpre)⟩
      · exact absurd e' e
  · rcases wt_get ht hu with ⟨rfl, rfl⟩ | ⟨hne, hu⟩
    · exact hT
    · exact hTo i u hne hu

variable {fuel : Nat}

/-- **An instruction step keeps the invariant.** -/
theorem inv_instr {outs : List (Except String (Outcome isa))} {oc : Outcome isa}
    (hs : stepOne Arch.armv8 t tid cfg.mem = some outs) (ho : .ok oc ∈ outs)
    (hc : CertOkN Arch.armv8 tid oc.thread oc.mem fuel) (hb : (cfg.withThread tid oc.thread oc.mem).Bnd) :
    LInv k N x o c (cfg.withThread tid oc.thread oc.mem) ∧
      ((fv oc.mem o = fv cfg.mem o ∧ oc.mem.lastWrite (L4 o) = cfg.mem.lastWrite (L4 o)) ∨
        fv oc.mem o = fv cfg.mem o + 1) := by
  have hT0 := h.thr tid t ht
  obtain ⟨hti', he⟩ := step_ti hT0.ti hs ho
  have he2 := he
  have hpre : cfg.mem.Prefix oc.mem := Memory.Prefix.stepOne hs ho
  have hnd' : NoDead oc.thread oc.mem := fun ts hts w hw => coh_lt_of_certOkN hc hts hw
  have hcnt' : countXP x oc.thread oc.mem ≤ phi oc.thread := by
    obtain ⟨t', m', hr, hq⟩ := hc
    exact cert_cnt (p := (oc.thread, oc.mem)) hr hq hti' h.hxo h.hxc
  have mkTS := fun hld => (⟨hti', oh_step hT0.ti hT0.oh h.xinj he2 h.hxo h.hoc hld, hnd', hcnt'⟩ :
    TS k x o c tid oc.thread oc.mem)
  have hfx := h.fx32
  have hfo := h.fo_le
  have hg : ∀ {ts w'}, cfg.mem.get? ts = some w' → oc.mem.get? ts = some w' := fun h' => by
    rw [hpre.get? (cfg.mem.last_le_of_get?_eq_some h')]; exact h'
  have hnd0 : ∀ ts ∈ oc.thread.prom, ∀ w, cfg.mem.get? ts = some w → oc.thread.views.getCoh w.loc < ts :=
    fun ts h1 w hw => hnd' ts h1 w (hg hw)
  have oldx : ∀ ts w', cfg.mem.get? ts = some w' → w'.loc = L4 x → w'.tid = tid →
      ∃ v, w'.val.toNat = v + 1 ∧ (OMsg o cfg.mem (v + 1) ∨ HoldsV x tid t cfg.mem v) := by
    intro ts w' hw hl e
    obtain ⟨v, u, hv, hu, hh⟩ := h.xheld ts w' hw hl
    rw [e] at hu hh; rw [ht] at hu; cases hu
    exact ⟨v, hv, hh⟩
  have oldo : ∀ ts w', cfg.mem.get? ts = some w' → w'.loc = L4 o → ∃ ts', XMsg x w'.tid oc.mem ts' w'.val.toNat :=
    fun ts w' hw hl => let ⟨ts', hx⟩ := h.oown ts w' hw hl; ⟨ts', hx.mono hpre⟩
  have hkeep : (Ticketed t → Ticketed oc.thread ∧ tk oc.thread = tk t) →
      (∀ ts ∈ t.prom, ∀ w, cfg.mem.get? ts = some w → w.loc = L4 x → ts ∈ oc.thread.prom) →
      ∀ ts w', oc.mem.get? ts = some w' → cfg.mem.get? ts = some w' → w'.loc = L4 x → w'.tid = tid →
      ∃ v, w'.val.toNat = v + 1 ∧ (OMsg o oc.mem (v + 1) ∨ HoldsV x tid oc.thread oc.mem v) := by
    intro h1 h2 ts w' _ hw hl e
    obtain ⟨v, hv, hh⟩ := oldx ts w' hw hl e
    refine ⟨v, hv, hh.imp (fun a => OMsg.mono a hpre) fun hH => ?_⟩
    rcases hH with ⟨a, b⟩ | ⟨ts2, h3, w2, hw2, hl2, hid2, hv2⟩
    · exact .inl ⟨(h1 a).1, (h1 a).2.trans b⟩
    · exact .inr ⟨ts2, h2 ts2 h3 w2 hw2 hl2, w2, hg hw2, hl2, hid2, hv2⟩
  -- `next` messages have values `v + 1`
  have xpos : ∀ ts w', cfg.mem.get? ts = some w' → w'.loc = L4 x → 1 ≤ w'.val.toNat := fun ts w' hw hl => by
    obtain ⟨v, u, hv, -⟩ := h.xheld ts w' hw hl; omega
  cases he with
  | quiet hm hp htk hk hn hw hphi hv =>
    refine build h ht hpre hb (.inl hm) (mkTS fun hne => absurd hm hne) ?_ (fun ts w hw hl e => ?_)
      (fun ts w hw hl e => ?_)
    · rw [hm, hn]; unfold countXP; rw [hp]
    · exact hkeep (fun a => ⟨htk.mpr a, hk a⟩) (fun ts h1 _ _ _ => hp ▸ h1) ts w hw (hm ▸ hw) hl e
    · exact e ▸ oldo ts w (hm ▸ hw) hl
  | ld tr old v hrd hwi h0 h1 hk hval hn hw hphi hv hcase =>
    rcases hcase with ⟨hm, hp, -, hco, hat⟩ | ⟨ts0, hts0, hg0, hm, hp, hc0, htr, hat⟩
    · -- fresh: the value `xc + 1`
      have hold := fresh_last hrd hwi hat hT0.ti.pcov (fun ts h1 => hp ▸ h1) hnd0 hco
      have htk' : tk oc.thread = fv cfg.mem x := by rw [hk, hold]; omega
      have hv1 : v.toNat = fv cfg.mem x + 1 := by rw [hval, htk']; omega
      refine build h ht hpre hb (.inr ⟨_, rfl, hm, fun _ => hv1, fun hx => absurd hx h.hxo⟩)
        (mkTS fun _ _ _ ts w hw hlo _ hvw => ?_) ?_ (fun ts w hw hl e => ?_) (fun ts w hw hl e => ?_)
      · have := h.ov' hw hlo; rw [htk'] at hvw; omega
      · rw [hm, hn, fv_app_eq _ _ _ rfl, countXP_mono (Memory.Prefix.append _ _) fun a ha => hT0.ti.wf a (hp ▸ ha)]
        unfold countXP; rw [hp]; dsimp only; omega
      · have hw' := hw; rw [hm] at hw'
        rcases cfg.mem.get?_append_eq_some _ hw' with ⟨-, hw0⟩ | ⟨-, rfl⟩
        · exact hkeep (fun a => absurd a h0) (fun ts h1 _ _ _ => hp ▸ h1) ts w hw hw0 hl e
        · exact ⟨_, hv1, .inr (.inl ⟨h1, htk'⟩)⟩
      · have hw' := hw; rw [hm] at hw'
        rcases cfg.mem.get?_append_eq_some _ hw' with ⟨-, hw0⟩ | ⟨-, rfl⟩
        · exact e ▸ oldo ts w hw0 hl
        · exact absurd hl h.hxo
    · -- fulfilment of a `next` promise
      have hx1 : 1 ≤ v.toNat := xpos _ _ hg0 rfl
      have hx2 : v.toNat ≤ fv cfg.mem x := h.xv' hg0 rfl
      have hlt := tk_lt oc.thread
      have hv1 : v.toNat = tk oc.thread + 1 := by
        have : v.toNat = (tk oc.thread + 1) % 2 ^ 32 := hval
        omega
      refine build h ht hpre hb (.inl hm) (mkTS fun hne => absurd hm hne) ?_ (fun ts w hw hl e => ?_)
        (fun ts w hw hl e => e ▸ oldo ts w (hm ▸ hw) hl)
      · have := countXP_erase (x := x) hp hts0 hg0
        simp only [↓reduceIte] at this
        rw [hm]; omega
      · obtain ⟨v', hv', hh⟩ := oldx ts w (hm ▸ hw) hl e
        refine ⟨v', hv', hh.imp (fun a => OMsg.mono a hpre) fun hH => ?_⟩
        rcases hH with ⟨a, -⟩ | ⟨ts2, h3, w2, hw2, hl2, hid2, hv2⟩
        · exact absurd a h0
        · by_cases e2 : ts2 = ts0
          · subst e2
            rw [hg0] at hw2; cases hw2
            have := h.xv' (hm ▸ hw) hl
            refine .inl ⟨h1, ?_⟩
            have : v.toNat = (v' + 1) % 2 ^ 32 := hv2
            omega
          · exact .inr ⟨ts2, by rw [hp]; exact (List.mem_erase_of_ne e2).mpr h3, w2, hg hw2, hl2, hid2, hv2⟩
  | st v htk hk hn hw hphi hv hcase =>
    have hkx : ∀ ts ∈ t.prom, ∀ w, cfg.mem.get? ts = some w → w.loc = L4 x → ts ∈ oc.thread.prom := by
      intro ts h1 w hw hl
      rcases hcase with ⟨-, hp, -⟩ | ⟨ts0, -, hg0, -, hp⟩
      · exact hp ▸ h1
      · rw [hp]; refine (List.mem_erase_of_ne fun e => ?_).mpr h1
        subst e; rw [hg0] at hw; cases hw; exact h.hxc hl.symm
    have hk' := hkeep (fun a => ⟨htk.mpr a, hk a⟩) hkx
    rcases hcase with ⟨hm, hp, -⟩ | ⟨ts0, hts0, hg0, hm, hp⟩
    · refine build h ht hpre hb (.inr ⟨_, rfl, hm, fun hx => absurd hx.symm h.hxc, fun hx => absurd hx.symm h.hoc⟩)
        (mkTS fun _ h0 h1 => absurd (htk.mp h1) h0) ?_ (fun ts w hw hl e => ?_) (fun ts w hw hl e => ?_)
      · rw [hm, hn, fv_app_ne _ _ _ (Ne.symm h.hxc),
          countXP_mono (Memory.Prefix.append _ _) fun a ha => hT0.ti.wf a (hp ▸ ha)]
        unfold countXP; rw [hp]
      · have hw' := hw; rw [hm] at hw'
        rcases cfg.mem.get?_append_eq_some _ hw' with ⟨-, hw0⟩ | ⟨-, rfl⟩
        · exact hk' ts w hw hw0 hl e
        · exact absurd hl.symm h.hxc
      · have hw' := hw; rw [hm] at hw'
        rcases cfg.mem.get?_append_eq_some _ hw' with ⟨-, hw0⟩ | ⟨-, rfl⟩
        · exact e ▸ oldo ts w hw0 hl
        · exact absurd hl.symm h.hoc
    · refine build h ht hpre hb (.inl hm) (mkTS fun hne => absurd hm hne) ?_
        (fun ts w hw hl e => hk' ts w hw (hm ▸ hw) hl e) (fun ts w hw hl e => e ▸ oldo ts w (hm ▸ hw) hl)
      have := countXP_erase (x := x) hp hts0 hg0
      simp only [Ne.symm h.hxc, ↓reduceIte] at this
      rw [hm, hn]; omega
  | rl v h0 h1 hval hord hn hw hphi hv hcase =>
    obtain ⟨ts1, -, w1, hw1, hl1, hid1, hv1⟩ := hT0.ti.txn h0
    have := xpos _ _ hw1 hl1
    have := tk_lt t
    have hk1 : tk t + 1 < 2 ^ 32 := by
      have : w1.val.toNat = (tk t + 1) % 2 ^ 32 := hv1
      omega
    have hvt : v.toNat = tk t + 1 := by
      have : v.toNat = (tk t + 1) % 2 ^ 32 := hval
      omega
    have hv1' : w1.val.toNat = tk t + 1 := by
      have : w1.val.toNat = (tk t + 1) % 2 ^ 32 := hv1
      omega
    have hkx : ∀ ts ∈ t.prom, ∀ w, cfg.mem.get? ts = some w → w.loc = L4 x → ts ∈ oc.thread.prom := by
      intro ts h2 w hw hl
      rcases hcase with ⟨-, hp, -⟩ | ⟨ts0, -, hg0, -, -, hp, -⟩
      · exact hp ▸ h2
      · rw [hp]; refine (List.mem_erase_of_ne fun e => ?_).mpr h2
        subst e; rw [hg0] at hw; cases hw; exact h.hxo hl.symm
    -- the released ticket's `owner` message
    have hom : OMsg o oc.mem (tk t + 1) := by
      rcases hcase with ⟨hm, -⟩ | ⟨ts0, -, hg0, -, hm, -⟩
      · exact ⟨_, _, by rw [hm]; exact Memory.get?_append_last _ _, rfl, hvt⟩
      · exact ⟨ts0, _, by rw [hm]; exact hg0, rfl, hvt⟩
    have hxt : ∀ ts w', oc.mem.get? ts = some w' → cfg.mem.get? ts = some w' → w'.loc = L4 x → w'.tid = tid →
        ∃ v, w'.val.toNat = v + 1 ∧ (OMsg o oc.mem (v + 1) ∨ HoldsV x tid oc.thread oc.mem v) := by
      intro ts w' _ hw hl e
      obtain ⟨v', hv', hh⟩ := oldx ts w' hw hl e
      refine ⟨v', hv', ?_⟩
      rcases hh with hh | ⟨a, b⟩ | ⟨ts2, h3, w2, hw2, hl2, hid2, hv2⟩
      · exact .inl (hh.mono hpre)
      · exact .inl (b ▸ hom)
      · exact .inr (.inr ⟨ts2, hkx ts2 h3 w2 hw2 hl2, w2, hg hw2, hl2, hid2, hv2⟩)
    rcases hcase with ⟨hm, hp, -, hco⟩ | ⟨ts0, hts0, hg0, -, hm, hp, -⟩
    · -- fresh: the value `M + 1`
      have hle : tk t ≤ fv cfg.mem o := by
        obtain ⟨tr, vv, hr, hvv, -⟩ := hord
        have := h.ov tr vv hr; have := Nat.mod_le vv.toNat (2 ^ 32); omega
      have htM : tk t = fv cfg.mem o := by
        refine Classical.byContradiction fun hne => ?_
        obtain ⟨ts', w', hw', hl', hv'⟩ := h.osurj (tk t) (by omega)
        obtain ⟨ts'', w'', hw'', hl'', hid'', hv''⟩ := h.oown ts' w' hw' hl'
        have e := h.xinj ts'' ts1 w'' w1 hw'' hw1 hl'' hl1 (by omega)
        subst e; rw [hw1] at hw''; cases hw''
        have hin := hT0.oh ts' w' hw' hl' (hid''.symm.trans hid1) (tk t) (by omega) (.inl ⟨h0, rfl⟩)
        have hd := hnd0 ts' (hp ▸ hin) w' hw'
        have := cfg.mem.last_le_of_get?_eq_some hw'
        rw [hl'] at hd; omega_t
      have hvo : v.toNat = fv cfg.mem o + 1 := by omega
      refine build h ht hpre hb (.inr ⟨_, rfl, hm, fun hx => absurd hx.symm h.hxo, fun _ => hvo⟩)
        (mkTS fun _ h0' _ => absurd h0 h0') ?_ (fun ts w hw hl e => ?_) (fun ts w hw hl e => ?_)
      · rw [hm, hn, fv_app_ne _ _ _ (Ne.symm h.hxo),
          countXP_mono (Memory.Prefix.append _ _) fun a ha => hT0.ti.wf a (hp ▸ ha)]
        unfold countXP; rw [hp]
      · have hw' := hw; rw [hm] at hw'
        rcases cfg.mem.get?_append_eq_some _ hw' with ⟨-, hw0⟩ | ⟨-, rfl⟩
        · exact hxt ts w hw hw0 hl e
        · exact absurd hl.symm h.hxo
      · have hw' := hw; rw [hm] at hw'
        rcases cfg.mem.get?_append_eq_some _ hw' with ⟨-, hw0⟩ | ⟨-, rfl⟩
        · exact e ▸ oldo ts w hw0 hl
        · exact ⟨ts1, w1, hg hw1, hl1, hid1, by rw [hv1', hvt]⟩
    · refine build h ht hpre hb (.inl hm) (mkTS fun hne => absurd hm hne) ?_
        (fun ts w hw hl e => hxt ts w hw (hm ▸ hw) hl e) (fun ts w hw hl e => e ▸ oldo ts w (hm ▸ hw) hl)
      have := countXP_erase (x := x) hp hts0 hg0
      simp only [Ne.symm h.hxo, ↓reduceIte] at this
      rw [hm, hn]; omega

/-- **A promise step keeps the invariant.** -/
theorem inv_prom {w : Msg} (hwt : w.tid = tid)
    (hc : CertOkN Arch.armv8 tid (promThread t cfg.mem w) (cfg.mem.append w).1 fuel)
    (hb : (cfg.withThread tid (promThread t cfg.mem w) (cfg.mem.append w).1).Bnd) :
    LInv k N x o c (cfg.withThread tid (promThread t cfg.mem w) (cfg.mem.append w).1) ∧
      ((fv (cfg.mem.append w).1 o = fv cfg.mem o ∧
        (cfg.mem.append w).1.lastWrite (L4 o) = cfg.mem.lastWrite (L4 o)) ∨
        fv (cfg.mem.append w).1 o = fv cfg.mem o + 1) := by
  have hT0 := h.thr tid t ht
  have hpre : cfg.mem.Prefix (cfg.mem.append w).1 := Memory.Prefix.append _ _
  have hti' := hT0.ti.prom w
  have hnd' : NoDead (promThread t cfg.mem w) (cfg.mem.append w).1 := fun ts hts w hw =>
    coh_lt_of_certOkN hc hts hw
  obtain ⟨tq, mq, hr, hq⟩ := hc
  have hcnt' := cert_cnt (p := (promThread t cfg.mem w, (cfg.mem.append w).1)) hr hq hti' h.hxo h.hxc
  have hfx := h.fx32
  have hfo := h.fo_le
  have hnew : cfg.mem.last + 1 ∈ (promThread t cfg.mem w).prom :=
    List.mem_append_right _ (by rw [Memory.append_time]; exact List.mem_singleton_self _)
  have hold : ∀ ts ∈ t.prom, ts ∈ (promThread t cfg.mem w).prom := fun ts h1 => List.mem_append_left _ h1
  have hw0 : (cfg.mem.append w).1.get? (cfg.mem.last + 1) = some w := Memory.get?_append_last _ _
  have hg : ∀ {ts w'}, cfg.mem.get? ts = some w' → (cfg.mem.append w).1.get? ts = some w' := fun h' => by
    rw [hpre.get? (cfg.mem.last_le_of_get?_eq_some h')]; exact h'
  have xpos : ∀ ts w', cfg.mem.get? ts = some w' → w'.loc = L4 x → 1 ≤ w'.val.toNat := fun ts w' hw hl => by
    obtain ⟨v, u, hv, -⟩ := h.xheld ts w' hw hl; omega
  -- a `next` promise has the value `xc + 1`
  have hxv : w.loc = L4 x → w.val.toNat = fv cfg.mem x + 1 := fun hl => by
    obtain ⟨tr, old, htr, hrd, hval, hno⟩ := cert_x (p := (promThread t cfg.mem w, (cfg.mem.append w).1)) hr hq hti'
      h.hxo h.hxc hnew hw0 hl
    have htr' : tr ≤ cfg.mem.last := by omega_t
    dsimp only at hrd hno
    rw [read?_append_of_le _ _ _ htr'] at hrd
    have hlw := read_lastWrite_of_coh cfg.mem (L4 x) htr' hrd (bound := cfg.mem.last) (by
      cases e : cfg.mem.writeIn (L4 x) tr cfg.mem.last with
      | false => rfl
      | true =>
        obtain ⟨ts, w', h1, h2, hw', hl'⟩ := (Memory.writeIn_iff _ _ _ _).mp e
        exact (hno ts w' (hg hw') hl' h1 (by omega_t)).elim) (cfg.mem.lastWrite_le _)
    rw [hval, hlw.2]; omega
  -- `OH` after the promise
  have hOH : OH x o tid (promThread t cfg.mem w) (cfg.mem.append w).1 := by
    intro ts w' hw' hlo hid v hv hH
    rcases cfg.mem.get?_append_eq_some w hw' with ⟨-, hw1⟩ | ⟨e, rfl⟩
    · refine hold _ (hT0.oh ts w' hw1 hlo hid v hv ?_)
      rcases hH with hH | ⟨ts2, h2, w2, hw2, hl2, hid2, hv2⟩
      · exact .inl hH
      · rcases List.mem_append.mp h2 with h2 | h2
        · exact .inr ⟨ts2, h2, w2, by rw [← hpre.get? (hT0.ti.wf ts2 h2)]; exact hw2, hl2, hid2, hv2⟩
        · exfalso
          rw [List.mem_singleton, Memory.append_time] at h2
          subst h2; rw [hw0] at hw2; cases hw2
          obtain ⟨ts3, w3, hw3, hl3, -, hv3⟩ := h.oown ts w' hw1 hlo
          have := h.xv' hw3 hl3
          have := hxv hl2
          omega
    · rw [e]; exact hnew
  -- an `owner` promise has the value `M + 1`
  have hov : w.loc = L4 o → w.val.toNat = fv cfg.mem o + 1 ∧
      ∃ ts1, XMsg x tid (cfg.mem.append w).1 ts1 w.val.toNat := fun hl => by
    obtain ⟨kk, tr, v, hrd, hkk, hval, ⟨ts1, w1, hw1, hl1, hid1, hv1⟩, huq⟩ :=
      cert_o (p := (promThread t cfg.mem w, (cfg.mem.append w).1)) hr hq hti' hOH
        (xinj_app h.xinj fun e => h.hxo (e.symm.trans hl)) h.hxo h.hoc hnew hw0 hl (Memory.last_append _ _).symm
    dsimp only at hrd hw1 huq
    have hw1' : cfg.mem.get? ts1 = some w1 := by
      rcases cfg.mem.get?_append_eq_some w hw1 with ⟨-, a⟩ | ⟨-, rfl⟩
      · exact a
      · exact absurd (hl1.symm.trans hl) h.hxo
    have := xpos _ _ hw1' hl1
    have hkl : kk + 1 < 2 ^ 32 := by omega
    have hkM : kk ≤ fv cfg.mem o := by
      rcases read?_append_eq_some _ _ hrd with hrd | ⟨-, -, rfl⟩
      · have := h.ov tr v hrd; have := Nat.mod_le v.toNat (2 ^ 32); omega
      · omega
    have hkM' : kk = fv cfg.mem o := by
      refine Classical.byContradiction fun hne => ?_
      obtain ⟨ts', w', hw', hl', hv'⟩ := h.osurj kk (by omega)
      obtain ⟨ts'', w'', hw'', hl'', hid'', hv''⟩ := h.oown ts' w' hw' hl'
      have e := h.xinj ts'' ts1 w'' w1 hw'' hw1' hl'' hl1 (by omega)
      subst e; rw [hw1'] at hw''; cases hw''
      have := huq ts' w' (hg hw') hl' (hid''.symm.trans hid1) (by omega)
      have := cfg.mem.last_le_of_get?_eq_some hw'
      omega_t
    exact ⟨by omega, ts1, w1, hw1, hl1, hid1, by omega⟩
  refine build h ht hpre hb (.inr ⟨w, hwt, rfl, hxv, fun hl => (hov hl).1⟩) ⟨hti', hOH, hnd', hcnt'⟩ ?_
    (fun ts w' hw' hl e => ?_) (fun ts w' hw' hl e => ?_)
  · rw [countXP_prom w hT0.ti.wf]
    show taken k t + _ + _ = taken k t + _ + _
    by_cases hl : w.loc = L4 x
    · rw [fv_app_eq _ _ _ hl, hxv hl, ite_eq_left hl]; omega
    · rw [fv_app_ne _ _ _ hl, ite_eq_right hl]; omega
  · rcases cfg.mem.get?_append_eq_some w hw' with ⟨-, hw1⟩ | ⟨-, rfl⟩
    · obtain ⟨v, u, hv, hu, hh⟩ := h.xheld ts w' hw1 hl
      rw [e] at hu hh; rw [ht] at hu; cases hu
      refine ⟨v, hv, hh.imp (fun a => OMsg.mono a hpre) fun hH => ?_⟩
      rcases hH with hH | ⟨ts2, h2, hx⟩
      · exact .inl hH
      · exact .inr ⟨ts2, hold ts2 h2, hx.mono hpre⟩
    · exact ⟨_, hxv hl, .inr (.inr ⟨_, hnew, w', hw0, hl, hwt, by rw [hxv hl]; omega⟩)⟩
  · rcases cfg.mem.get?_append_eq_some w hw' with ⟨-, hw1⟩ | ⟨-, rfl⟩
    · obtain ⟨ts', hx⟩ := h.oown ts w' hw1 hl
      exact ⟨ts', e ▸ hx.mono hpre⟩
    · exact (hov hl).2

/-- **A semantic step keeps the invariant**; `owner` keeps its value and its
last write, or grows by one. -/
theorem inv_step {cfg' : Config isa} (hst : StepSem Arch.armv8 fuel tid cfg cfg') :
    LInv k N x o c cfg' ∧ ((fv cfg'.mem o = fv cfg.mem o ∧ cfg'.mem.lastWrite (L4 o) = cfg.mem.lastWrite (L4 o)) ∨
      fv cfg'.mem o = fv cfg.mem o + 1) := by
  have hb := h.bnd.semStep hst
  rcases hst with ⟨t1, outs, oc, ht1, hs, ho, hc, rfl⟩ | ⟨t1, w, ht1, hwt, hc, rfl⟩
  · rw [ht] at ht1; cases ht1
    exact inv_instr h ht hs ho hc hb
  · rw [ht] at ht1; cases ht1
    exact inv_prom h ht hwt hc hb

end Pres

/-! ## Initially and along traces -/

/-- **The invariant holds initially.** -/
theorem inv_init {k N : Nat} {x o c : BitVec 64} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : TkLoopStart k N x o c states initMem) : LInv k N x o c (Config.init states initMem) := by
  have hthr : ∀ (i : Nat) t, (Config.init states initMem : Config isa).threads[i]? = some t →
      ∃ s ∈ states, t = Thread.init s := fun i t h => by
    simp only [Config.init, List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at h
    obtain ⟨s, hs, rfl⟩ := h
    exact ⟨s, List.mem_of_getElem? hs, rfl⟩
  have hget : ∀ ts w, (Config.init states initMem : Config isa).mem.get? ts = some w → False := by
    intro ts w h; simp [Memory.get?, Config.init] at h
  have hfx : fv (Config.init states initMem : Config isa).mem x = 0 := by
    have := hs.hX0; simp only [Memory.finalVal, Config.init] at this ⊢; simp [this]
  have hfo : fv (Config.init states initMem : Config isa).mem o = 0 := by
    have := hs.hO0; simp only [Memory.finalVal, Config.init] at this ⊢; simp [this]
  have hrd : ∀ (a : BitVec 64) ts v, (Config.init states initMem : Config isa).mem.read? (L4 a) ts = some v →
      ts = 0 ∧ v = (Config.init states initMem : Config isa).mem.initVal (L4 a) := by
    intro a ts v h
    rcases Memory.read?_eq_some _ h with ⟨rfl, e⟩ | ⟨w, hw, -, -⟩
    · exact ⟨rfl, e⟩
    · exact (hget _ _ hw).elim
  have hprom : ∀ (i : Nat) t, (Config.init states initMem : Config isa).threads[i]? = some t → t.prom = [] :=
    fun i t h => by obtain ⟨s, -, rfl⟩ := hthr i t h; rfl
  refine ⟨by simp [Config.init, hs.hN], hs.hNk32, SpinStep.loc_ne hs.hxo, SpinStep.loc_ne hs.hxc,
    SpinStep.loc_ne hs.hoc, Config.init_bnd _ _,
    fun ts v h => ?_, fun ts v h => ?_, fun _ _ _ _ h => (hget _ _ h).elim, fun _ _ _ _ h => (hget _ _ h).elim,
    fun k hk => absurd hk (by omega), fun k hk => absurd hk (by omega), fun _ _ h => (hget _ _ h).elim,
    fun _ _ h => (hget _ _ h).elim, ?_, fun i t h => ?_⟩
  · obtain ⟨-, rfl⟩ := hrd x ts v h; rw [hfx]; have := hs.hX0; simp only [Config.init] at this ⊢; simp [this]
  · obtain ⟨-, rfl⟩ := hrd o ts v h; rw [hfo]; have := hs.hO0; simp only [Config.init] at this ⊢; simp [this]
  · have := tsum_le (c := (Config.init states initMem : Config isa))
      (F := fun _ t => taken k t + countXP x t (Config.init states initMem : Config isa).mem) (M := 0)
      fun i u hu => by
        obtain ⟨s, hm, rfl⟩ := hthr i u hu
        have hpc : (Thread.init s : Thread isa).st.st.2 = pcA 1 := (hs.hst s hm).pc.trans addrOf_0
        rw [taken_at (by decide) hpc]
        have h7 := (hs.hst s hm).x7
        show k - wn s.st.1.regs.X7 + (if 1 ∈ tkBusy then 1 else 0) + countXP x (Thread.init s) _ ≤ 0
        rw [h7]; simp [tkBusy, countXP, Thread.init]
    omega
  · obtain ⟨s, hm, rfl⟩ := hthr i t h
    have hst := hs.hst s hm
    have hpc : (Thread.init s : Thread isa).st.st.2 = pcA 1 := hst.pc.trans addrOf_0
    have hp0 : (Thread.init s : Thread isa).prom = [] := rfl
    refine ⟨ti_of (j := 1) (by decide) hpc ⟨⟨hst.exe, hst.decls, hst.endPc, hst.x0, hst.x1, hst.x2, hst.dx, hst.dO,
      hst.dc⟩, 1, by decide, hpc⟩ ⟨.inl hpc, fun h => (pc_ne hpc h (by decide) (by decide) (by decide)).elim⟩
      (Nat.le_of_eq hst.x7) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun h => absurd h (by decide)) (fun ts w hw => (hget _ _ hw).elim) ((Config.init_wf _ _ i _ h).1)
      (by simp [hp0]) (by simp [hp0]), fun ts w hw => (hget _ _ hw).elim, fun ts hts => by simp [hp0] at hts, ?_⟩
    simp [countXP, hp0]

/-- **The invariant along a semantic trace from a start configuration.** -/
theorem trace_linv {fuel k N : Nat} {x o c : BitVec 64} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : TkLoopStart k N x o c states initMem) (tr : TraceSem Arch.armv8 fuel isa)
    (h0 : tr.cfg 0 = Config.init states initMem) : ∀ i, LInv k N x o c (tr.cfg i)
  | 0 => h0 ▸ inv_init hs
  | i + 1 => by
    have h := trace_linv hs tr h0 i
    rcases tr.step i with ⟨tid, hst⟩ | ⟨-, he⟩
    · obtain ⟨t, ht⟩ : ∃ t, (tr.cfg i).threads[tid]? = some t := by
        rcases hst with ⟨t, -, -, ht, -⟩ | ⟨t, -, ht, -⟩ <;> exact ⟨t, ht⟩
      exact (inv_step h ht hst).1
    · rw [he]; exact h

/-- **`owner` along a semantic trace**: it keeps its value and its last write,
or grows by one. -/
theorem trace_o {fuel k N : Nat} {x o c : BitVec 64} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : TkLoopStart k N x o c states initMem) (tr : TraceSem Arch.armv8 fuel isa)
    (h0 : tr.cfg 0 = Config.init states initMem) (i : Nat) :
    (fv (tr.cfg (i + 1)).mem o = fv (tr.cfg i).mem o ∧
      (tr.cfg (i + 1)).mem.lastWrite (L4 o) = (tr.cfg i).mem.lastWrite (L4 o)) ∨
      fv (tr.cfg (i + 1)).mem o = fv (tr.cfg i).mem o + 1 := by
  rcases tr.step i with ⟨tid, hst⟩ | ⟨-, he⟩
  · obtain ⟨t, ht⟩ : ∃ t, (tr.cfg i).threads[tid]? = some t := by
      rcases hst with ⟨t, -, -, ht, -⟩ | ⟨t, -, ht, -⟩ <;> exact ⟨t, ht⟩
    exact (inv_step (trace_linv hs tr h0 i) ht hst).2
  · rw [he]; exact .inl ⟨rfl, rfl⟩

/-! ## F3 without the bound hypothesis -/

/-- **F3: the holder of ticket `M` certifies without fresh writes** (semantic
machine; `holder_nacert` with `M + 1 < 2 ^ 32` discharged by the trace
invariant: `M` is `owner`'s value, at most `next`'s, at most `N * k`). -/
theorem holder_nacert' {fuel k N : Nat}
    {x o c : BitVec 64} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : TkLoopStart k N x o c states initMem) (tr : TraceSem Arch.armv8 fuel isa)
    (h0 : tr.cfg 0 = Config.init states initMem) (i : Nat) {H M : Nat} {u : Thread isa}
    (hu : (tr.cfg i).threads[H]? = some u)
    (hM : ((tr.cfg i).mem.finalVal (L4 o)).toNat = M)
    (hh : HoldsLoop x u (tr.cfg i).mem M)
    (hno : ∀ ts w, (tr.cfg i).mem.get? ts = some w → w.loc = L4 o → w.val.toNat ≠ M + 1)
    (hc : CertOkN Arch.armv8 H u (tr.cfg i).mem fuel) :
    u.prom = [] ∨ NACertG Arch.armv8 fuel H u (tr.cfg i).mem :=
  have h := trace_linv hs tr h0 i
  holder_nacert hs tr h0 i hu hM hh hno hc (by have := h.fo_le; have := h.fx32; omega)

/-- **F3 for a holder in the sense of `HoldsV`** (taken, or reserved by an
outstanding `next` promise of its own, whether or not it has taken a ticket
since): no promise, or a certification without fresh writes. -/
theorem holder_nacertV {fuel k N : Nat}
    {x o c : BitVec 64} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : TkLoopStart k N x o c states initMem) (tr : TraceSem Arch.armv8 fuel isa)
    (h0 : tr.cfg 0 = Config.init states initMem) (i : Nat) {H M : Nat} {u : Thread isa}
    (hu : (tr.cfg i).threads[H]? = some u)
    (hh : HoldsV x H u (tr.cfg i).mem M) (hM : M ≤ fv (tr.cfg i).mem x)
    (hno : ∀ ts w, (tr.cfg i).mem.get? ts = some w → w.loc = L4 o → w.val.toNat ≠ M + 1)
    (hc : CertOkN Arch.armv8 H u (tr.cfg i).mem fuel) :
    u.prom = [] ∨ NACertG Arch.armv8 fuel H u (tr.cfg i).mem := by
  by_cases hp0 : u.prom = []
  · exact .inl hp0
  right
  have h := trace_linv hs tr h0 i
  have hM32 : M + 1 < 2 ^ 32 := by have := h.fx32; omega
  obtain ⟨hf, hwf⟩ := trace_wf tr h0 i H u hu
  have hP : Phase x o c M u (tr.cfg i).mem :=
    ⟨trace_sinv hs tr h0 i H u hu, trace_reginv hs tr h0 i H u hu, hf, hwf, hno,
      hh.imp id fun ⟨ts, hts, w, hw, hl, _, hv⟩ => ⟨ts, hts, w, hw, hl, by omega⟩⟩
  obtain ⟨t', m', hr, hq⟩ := hc
  exact phase_run h.hxo h.hxc hM32 hr hq hP

end Kraken.Promising.Live.TicketLoopInvP
