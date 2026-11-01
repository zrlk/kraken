/-
**Certification inside the print phase** (C4, relation half; data in
`Spike/Lib/HelloW1.lean`): while it prints, the worker may hold its
promise of `c`'s `1` only past the last byte's `emit` (WeakCore 621ec97a:
an extern step needs no promise, so no promise is held across an `emit`;
`NoEmit`). It is certified by a solo frame run to `print`'s return and the
return to the store, which fulfils it (`WorkerSrc.certified_store`).

The view-growth part (`ldVs`, `VB`, `ck_ld`) is kept for a run through the
buffer's loads: the loads read the buffer words' latest messages (`hM`)
and grow the worker's views only by those messages' `pairTop`s and views,
at most `S - 1` (`hRd`); the buffer words are not `c`'s (`hne`). So the
store's view and ordering bound at the store are at most those at the
start joined with `S - 1` (`VB`, `vb_storeMview`, `vb_storeOb`).

- `ldVs`, `loadUnits_one_vs`, `src_load_vs`: the plain load of the latest
  message, with the views it leaves;
- `VB`, `vb_refl`, `vb_ld`, `vb_storeMview`, `vb_storeOb`: the view growth
  along the run;
- `CE`, `CertH`, `CK`: the thread's frame, promise and views along the
  run, and certification from a control;
- `ck_run`, `ck_ret`, `ck_ld`: back along a local run, from `print`'s
  return, over a load;
- `solo_frameRun`: a frame run is a solo run;
- `certified_printPh`: with no `emit` ahead (`NoEmit`) and one promise of
  `c`'s `1`, the worker is certified (the buffer, `BufV`, is not read).
-/
import Spike.Lib.HelloW1Anchor
import Spike.Lib.WorkerSrc

namespace Spike.Lib.HelloW1

open CoreLang CoreTerm TermRun TermExtStep
open Spike.Lib
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloSplit (envP wcP workerRestH workerCallH)
open Spike.Lib.HelloPrintSrcPub (PrintCP loadCP ldCP laneCP emitCP nextCP elemW printLPD_find printPD_find callTh)
open Spike.Lib.PrintSrc (printN printBody printLane printNext)
open Spike.Lib.WorkerSrc (wTh one AtStore certified_store)
open Spike.Lib.WorkerSrcStep (getElem?_set!_self localRunS_solo certified_of_solo)
open Scc.Sem.MemRel (SLatest)

/-! ## The plain load, with its views -/

/-- The views a plain load of message `t` (of view `mv`) at `a` leaves
(`Promises.stepLoad`, not acquiring). -/
def ldVs (vs : WeakMem.VState) (pairs : List Nat) (a : WeakMem.Address) (t mv : Nat) : WeakMem.VState :=
  { vs with coh := fun b => if b = a then max (vs.coh a) t else vs.coh b,
            vRd := max vs.vRd (Promises.rdV vs pairs t mv) }

/-- **One unit's plain load of the latest message**, with the views it
leaves (`SrcMem.loadUnits_one`). -/
theorem loadUnits_one_vs (arch : WeakMem.Arch) (pw : Word) {a : WeakMem.Address} (s : St) {j : Nat}
    {m : WeakMem.Msg} (hj : SLatest s.mem a j) (hm : s.mem[j]? = some m) :
    ({ s with vs := ldVs s.vs s.pairs a j m.view, undefs := s.undefs + countUndef [⟨m.val, m.view, j⟩] },
      [⟨m.val, m.view, j⟩]) ∈ loadUnits arch pw a false [.one] 0 s := by
  have hjs : j < s.mem.size := (Array.getElem?_eq_some_iff.mp hm).1
  have hmj : s.mem[j]! = m := by
    rw [getElem!_pos s.mem j hjs]; exact (Array.getElem?_eq_some_iff.mp hm).2
  simp only [loadUnits, SrcMem.offs_zero, List.mem_flatMap, List.mem_map]
  refine ⟨_, List.mem_map.mpr ⟨j, List.mem_filter.mpr ⟨List.mem_range.mpr hjs,
    Scc.Sem.MemRel.readable_latest hj⟩, rfl⟩, _, List.mem_singleton.mpr rfl, ?_⟩
  simp [hmj, ldVs, mth]

/-- **The source load of a one-word cell, with its views**: at
`let x = load false l in e`, the thread can read the latest message `j` of
the cell, binding its word, its views growing by `ldVs`. -/
theorem src_load_vs (g : G) (mem : WeakMem.Memory) (pairs : List Nat) (th : TTh)
    {x : String} {l : At} {e : Expr} {μ : Mode} {sg : Bool} {w : Wd} {pw : Word} {a : WeakMem.Address} {gg : Nat}
    {j : Nat} {m : WeakMem.Msg}
    (ht : th.term = .let_ x (.load false l) e) (hel : evalAt th.env l = some (.loc μ (.lanes sg w), [pw]))
    (hpw : pw.val = .loc a gg) (hj : SLatest mem a j) (hm : mem[j]? = some m) :
    (mem, pairs, { th with term := e, env := (x, .lanes sg w, [⟨m.val, m.view, j⟩]) :: th.env,
                           vs := ldVs th.vs pairs a j m.view,
                           undefs := th.undefs + countUndef [⟨m.val, m.view, j⟩] }) ∈ tstep g mem pairs th := by
  have hl := loadUnits_one_vs g.arch pw (stOf mem pairs th) hj hm
  simp only [tstep, ht, evalOp, hel, cellOf, addrOf, hpw, wordOf, accs, List.mem_map]
  exact ⟨_, ⟨_, hl, rfl⟩, rfl⟩

/-! ## The view growth -/

/-- **The views along the run**, from `vs0`: as at the start but for the
coherence views off `cS` and `vRd`, which grows at most to `S - 1`. -/
structure VB (S : Nat) (cS : WeakMem.Address) (vs0 vs : WeakMem.VState) : Prop where
  coh : vs.coh cS = vs0.coh cS
  vRd : vs.vRd ≤ max vs0.vRd (S - 1)
  vWr : vs.vWr = vs0.vWr
  vCtrl : vs.vCtrl = vs0.vCtrl
  vPreBase : vs.vPreBase = vs0.vPreBase
  vRelSt : vs.vRelSt = vs0.vRelSt

theorem vb_refl (S : Nat) (cS : WeakMem.Address) (vs : WeakMem.VState) : VB S cS vs vs :=
  ⟨rfl, Nat.le_max_left _ _, rfl, rfl, rfl, rfl⟩

/-- **A plain load off `cS`** of a message whose `pairTop` and view are at
most `S - 1` keeps `VB`. -/
theorem vb_ld {S : Nat} {cS a : WeakMem.Address} {vs0 vs : WeakMem.VState} {pairs : List Nat} {t mv : Nat}
    (h : VB S cS vs0 vs) (ha : a ≠ cS) (hp : Promises.pairTop pairs t ≤ S - 1) (hv : mv ≤ S - 1) :
    VB S cS vs0 (ldVs vs pairs a t mv) := by
  refine ⟨?_, ?_, h.vWr, h.vCtrl, h.vPreBase, h.vRelSt⟩
  · show (if cS = a then _ else vs.coh cS) = _
    rw [ite_eq_right_iff.mpr (fun e => absurd e.symm ha)]
    exact h.coh
  · show max vs.vRd (Promises.rdV vs pairs t mv) ≤ _
    exact Nat.max_le.mpr ⟨h.vRd, Nat.le_trans (Promises.rdV_le vs pairs t mv)
      (Nat.le_trans (Nat.max_le.mpr ⟨hp, hv⟩) (Nat.le_max_right _ _))⟩

private theorem max_aux1 {a r r0 b d S : Nat} (hr : r ≤ max r0 S) :
    max (max a (max r b)) d ≤ max (max (max a (max r0 b)) d) S := by omega

private theorem max_aux2 {x r r0 b S : Nat} (hr : r ≤ max r0 S) :
    max x (max r b) ≤ max (max x (max r0 b)) S := by omega

/-- **The store's view** at the end of the run is at most the start's,
joined with `S - 1`. -/
theorem vb_storeMview {S : Nat} {cS : WeakMem.Address} {vs0 vs : WeakMem.VState} (h : VB S cS vs0 vs) (cw : Word) :
    Promises.storeMview (wTh vs cw) (dataE 1 one) [0] true ≤
      max (Promises.storeMview (wTh vs0 cw) (dataE 1 one) [0] true) (S - 1) := by
  have hr := h.vRd
  simp only [Promises.storeMview, wTh, h.vRelSt, h.vWr, ite_true]
  exact max_aux1 hr

/-- **The store's ordering bound** at the end of the run is at most the
start's, joined with `S - 1`. -/
theorem vb_storeOb {S : Nat} {cS : WeakMem.Address} {vs0 vs : WeakMem.VState} (h : VB S cS vs0 vs)
    (kn : Promises.Knobs) (arch : WeakMem.Arch) (cw : Word) :
    Promises.storeOb kn arch (wTh vs cw) cS (dataE 1 one) [0] ≤
      max (Promises.storeOb kn arch (wTh vs0 cw) cS (dataE 1 one) [0]) (S - 1) := by
  have hr := h.vRd
  simp only [Promises.storeOb, wTh, h.vPreBase, h.vCtrl, h.coh, h.vWr]
  split
  · exact max_aux2 hr
  · exact Nat.le_max_left _ _

/-! ## Certification along the run -/

/-- The data of the run: `S`, `c`'s address, the memory and the paired
timestamps (unchanged along the run), the views at the start, the frame of
`print`'s call, the promise. -/
structure CE where
  S : Nat
  cS : WeakMem.Address
  mem0 : WeakMem.Memory
  pairs0 : List Nat
  vs0 : WeakMem.VState
  fr : Frame
  t : Nat

/-- **The thread along the run**: thread 1, inside `print` on the call's
frame, no type variables, the one promise, the views grown by `VB`; the
memory and the paired timestamps as at the start. -/
structure CertH (E : CE) (s : Cfg) (th : TTh) : Prop where
  get : s.ths[1]? = some th
  mem : s.mem = E.mem0
  pairs : s.pairs = E.pairs0
  stack : th.stack = [E.fr]
  σs : th.σs = []
  prom : th.promises = [E.t]
  vb : VB E.S E.cS E.vs0 th.vs

/-- **Certification from a control**: thread 1 at the control, along the
run, is certified. -/
def CK (kn : Promises.Knobs) (arch : WeakMem.Arch) (E : CE) (c : Ctl) : Prop :=
  ∀ s th, CertH E s th → th.term = c.term → th.env = c.env → Certified helloSrc kn arch s 1

variable {kn : Promises.Knobs} {arch : WeakMem.Arch} {E : CE}

/-- **Back along a local run.** -/
theorem ck_run {c c' : Ctl} (hr : LocalRunS helloSrc c c') (hk : CK kn arch E c') : CK kn arch E c := by
  intro s th h ht he
  have hs := localRunS_solo (k := kn) (arch := arch) hr h.get ht he h.σs
  exact certified_of_solo hs (hk _ _ ⟨getElem?_set!_self h.get _, h.mem, h.pairs, h.stack, h.σs, h.prom, h.vb⟩ rfl rfl)

/-- **At `print`'s return**: the return pops the call's frame, landing at
the store (`wkStore`, `c` bound to `cw`), which fulfils the promise
(`certified_store`) when the promise's message covers the start's store
view and is above its ordering bound, joined with `S - 1`. -/
theorem ck_ret {w0 w1 w2 w4 cw : Word} {w : Nat} (hfr : E.fr = uFrame w0 w1 w2 cw w4) (hcw : cw.val = .loc E.cS 0)
    (hm : E.mem0[E.t]? = some ⟨E.cS, .num 1, w⟩)
    (hmv : max (Promises.storeMview (wTh E.vs0 cw) (dataE 1 one) [0] true) (E.S - 1) ≤ w)
    (hob : max (Promises.storeOb kn arch (wTh E.vs0 cw) E.cS (dataE 1 one) [0]) (E.S - 1) < E.t) (env : Env) :
    CK kn arch E ⟨.ret .unit, env, none⟩ := by
  intro s th h ht _
  have hst : th.stack = [uFrame w0 w1 w2 cw w4] := hfr ▸ h.stack
  have hmem : (s.mem, s.pairs, SrcCalls.popTh th (uFrame w0 w1 w2 cw w4) [] []) ∈
      tstep (gOf helloSrc kn arch s 1) s.mem s.pairs th := by
    rw [tstep_ret (a := .unit) (t := .unit) (ws := []) ht hst rfl]
    exact List.mem_singleton.mpr rfl
  refine certified_of_solo (.thread (SrcMem.mem_threadSteps h.get hmem) (.refl _)) ?_
  have hA : AtStore cw E.cS (SrcCalls.popTh th (uFrame w0 w1 w2 cw w4) [] []) :=
    ⟨rfl, rfl, rfl, ⟨.ptr .pub .int, .pub, .int,
      by simp [SrcCalls.popTh, uFrame, envP, evalAt, lookupE], rfl, rfl⟩, hcw⟩
  refine certified_store (p := helloSrc) (getElem?_set!_self h.get _) hA h.prom ?_
    (Nat.le_trans (vb_storeMview h.vb cw) hmv) (Nat.lt_of_le_of_lt (vb_storeOb h.vb kn arch cw) hob)
  show s.mem[E.t]? = _
  rw [h.mem]; exact hm

/-- **Back over the load** of word `i` of the buffer: the load reads its
latest message (`hM`), whose `pairTop` and view are at most `S - 1`
(`hRd`), the word not `c`'s (`hne`). -/
theorem ck_ld {pw wn : Word} {l : WeakMem.AllocLabel} {m k i v : Nat}
    (hM : ∃ j msg, SLatest E.mem0 ⟨l, i⟩ j ∧ E.mem0[j]? = some msg ∧ msg.val = .num v)
    (hRd : ∀ j msg, SLatest E.mem0 ⟨l, i⟩ j → E.mem0[j]? = some msg →
      Promises.pairTop E.pairs0 j ≤ E.S - 1 ∧ msg.view ≤ E.S - 1)
    (hne : (⟨l, i⟩ : WeakMem.Address) ≠ E.cS)
    (hk : ∀ mw : Word, mw.val = .num v → CK kn arch E (laneCP pw wn m k (elemW pw l i) mw)) :
    CK kn arch E (ldCP pw wn m k (elemW pw l i)) := by
  intro s th h ht he
  obtain ⟨j, msg, hj, hmsg, hv⟩ := hM
  obtain ⟨hp, hvw⟩ := hRd j msg hj hmsg
  rw [← h.mem] at hj hmsg
  rw [← h.pairs] at hp
  have hstep := src_load_vs (gOf helloSrc kn arch s 1) s.mem s.pairs th (x := "wd") (l := .var "l") (e := printLane)
    (μ := .pub) (sg := false) (w := .w8) (pw := elemW pw l i) (a := ⟨l, i⟩) (gg := 0) ht (by rw [he]; rfl) rfl hj hmsg
  refine certified_of_solo (.thread (SrcMem.mem_threadSteps h.get hstep) (.refl _))
    (hk ⟨msg.val, msg.view, j⟩ hv _ _ ⟨getElem?_set!_self h.get _, h.mem, h.pairs, h.stack, h.σs, h.prom,
      vb_ld h.vb hne hp hvw⟩ rfl ?_)
  show _ :: th.env = _
  rw [he]; rfl

/-! ## The print phase is certified -/

/-- **A frame run of thread `i` is a solo run** (no type variables;
`HelloStep1P.frameRun_solo`'s twin, below it in the imports). -/
theorem solo_frameRun {i : Nat} {q q' : Ctl × List Frame} (h : FrameRun helloSrc q q') :
    ∀ {s : Cfg} {th : TTh}, s.ths[i]? = some th → th.term = q.1.term → th.env = q.1.env →
      th.σs = [] → th.stack = q.2 →
      Solo helloSrc kn arch i s
        { s with ths := s.ths.set! i { th with term := q'.1.term, env := q'.1.env, stack := q'.2 } } := by
  induction h with
  | refl q =>
    intro s th hi ht he _ hst
    have e1 : { th with term := q.1.term, env := q.1.env, stack := q.2 } = th := by rw [← ht, ← he, ← hst]
    have e2 : s.ths.set! i th = s.ths := by
      obtain ⟨hlt, hx⟩ := Array.getElem?_eq_some_iff.mp hi
      subst hx
      simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds, hlt]
    rw [e1, e2]
    exact .refl _
  | @step q q₁ q' hs _ ih =>
    intro s th hi ht he hσ hst
    let th₁ : TTh := { th with term := q₁.1.term, env := q₁.1.env, stack := q₁.2 }
    have hm : { s with ths := s.ths.set! i th₁ } ∈ threadSteps helloSrc kn arch s i :=
      tstep_mem_threadSteps hi (hs.tstep rfl ht he hσ hst)
    have h2 := ih (s := { s with ths := s.ths.set! i th₁ }) (getElem?_set!_self hi th₁) rfl rfl hσ rfl
    simp only [th₁, set!_set!] at h2
    exact .thread hm h2



/-- **The worker with no `emit` ahead is certified**: thread 1 with a
frame run to `print`'s return (`NoEmit`), no type variables and the one
promise `t`, a message of `c`'s `1` at view `w`, whose store view and
ordering bound at the worker's views are at most `w` and below `t`. The run
reads no memory and keeps the views, so the buffer (`BufV`) is not read:
the run through the loads and `emit`s is not needed, as no promise is held
across an `emit` (WeakCore 621ec97a: an extern step needs no promise). -/
theorem certified_printPh {cw : Word} {s : Cfg} {s1 : TTh} {cS : WeakMem.Address} {t w : Nat}
    (hN : NoEmit cw s1) (hi : s.ths[1]? = some s1) (hσ : s1.σs = []) (hp : s1.promises = [t])
    (hmt : s.mem[t]? = some ⟨cS, .num 1, w⟩) (hcw : cw.val = .loc cS 0)
    (hmv : Promises.storeMview (wTh s1.vs cw) (dataE 1 one) [0] true ≤ w)
    (hob : Promises.storeOb kn arch (wTh s1.vs cw) cS (dataE 1 one) [0] < t) :
    Certified helloSrc kn arch s 1 := by
  obtain ⟨w0, w1, w2, w4, env, -, hr⟩ := hN
  let E : CE := ⟨1, cS, s.mem, s.pairs, s1.vs, uFrame w0 w1 w2 cw w4, t⟩
  have hret : CK kn arch E ⟨.ret .unit, env, none⟩ :=
    ck_ret (E := E) rfl hcw hmt (Nat.max_le.mpr ⟨hmv, Nat.zero_le w⟩)
      (Nat.max_lt.mpr ⟨hob, Nat.lt_of_lt_of_le (Nat.zero_lt_of_lt hob) (Nat.le_refl t)⟩) env
  refine certified_of_solo (solo_frameRun hr hi rfl rfl hσ rfl) (hret _ _ ⟨getElem?_set!_self hi _, rfl, rfl,
    rfl, hσ, hp, vb_refl _ _ _⟩ rfl rfl)

/-- info: 'Spike.Lib.HelloW1.certified_printPh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certified_printPh

end Spike.Lib.HelloW1
