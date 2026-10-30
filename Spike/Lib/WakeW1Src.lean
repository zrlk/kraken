/-
**The source worker's local moves after the spawn** (data in `Spike/Lib/WakeW1.lean`).

The source worker runs `wkTail` (its spawn: the tail call of `worker`),
`wkBody` (`split a c j`), `wkStore`, `wkUnpark`, `ret `. Only the first
two take local steps; the store writes memory, `unpark` is an extern and
`ret ` on one frame has no step.

- `WCtl cw c`: the worker's control invariant (no hold, a worker term, its
  environment: `EnvBody` before the split, `EnvCJ` after).
- `localStep_wCtl`, `localRun_wCtl`: a local step / run keeps `WCtl`.
- `localRunS_store`: before its store the worker runs locally to its store
  (`AtStore`), its other fields kept.
- `certified_pre`: before its store, with its one promise a message of `c`'s
  `1` at a view covering the store's and above its ordering bound, the
  worker is certified (the run to the store, then the fulfilment).
- `SmGrow`, `srcStep_sm_mono`: how a source step of the worker changes the
  source memory (kept, or one message pushed): the hypothesis `hsm` of
  `Inv2Core.core1_append`, given by the step lemmas.
-/
import Spike.Lib.WakeW1
import Spike.Lib.SegS

namespace Spike.Lib.WakeW1

open CoreLang CoreTerm TermRun
open Kraken.Promising Scc.Sem Scc.Sem.SrcSem
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeT1 Spike.Lib.WorkerSrc Spike.Lib.WorkerSrcStep

/-! ## The source memory's growth -/

/-- **How a worker source step changes the source memory**: kept, or one
message pushed (`Inv2Core.core1_append`'s `hsm`). -/
def SmGrow (sm sm' : WeakMem.Memory) : Prop := sm' = sm ∨ ∃ m, sm' = sm.push m

theorem SmGrow.refl (sm : WeakMem.Memory) : SmGrow sm sm := .inl rfl

theorem SmGrow.push (sm : WeakMem.Memory) (m : WeakMem.Msg) : SmGrow sm (sm.push m) := .inr ⟨m, rfl⟩

/-- **The source memory after a worker source step**: a step that keeps the
source memory (a local run, the fulfilling store, `unpark`) or pushes one
message (the appending store, the promise) is `SmGrow`. -/
theorem srcStep_sm_mono {sm sm' : WeakMem.Memory} (h : sm' = sm ∨ ∃ m, sm' = sm.push m) : SmGrow sm sm' := h

/-! ## The worker's declaration -/

/-- The worker's argument type. -/
def wkArgTy : Ty := .prod (.ptr .pub .int) .tid

/-- **`worker` in `wakeSrc`**: argument `a` of type `wkArgTy`, body `wkBody`. -/
theorem wakeSrc_find_worker :
    ∃ d, wakeSrc.find? (·.name == "worker") = some d ∧ d.arg = "a" ∧ d.argTy = wkArgTy ∧ d.body = wkBody :=
  ⟨_, rfl, rfl, rfl, rfl⟩

/-- `EnvBody` at the worker's entry environment. -/
theorem envBody_entry {cw jw : Word} (hj : jw.val = mainTidW) : EnvBody cw [("a", wkArgTy, [cw, jw])] :=
  ⟨.ptr .pub .int, .tid, [.one], jw, by simp [evalAt, lookupE, wkArgTy], rfl, rfl, ⟨.pub, .int, rfl, rfl⟩, hj⟩

/-! ## The control invariant -/

/-- **The worker's control invariant**: no hold, a worker term, `c`'s and
`j`'s words in the environment (`EnvBody` before the split, `EnvCJ`
after). -/
structure WCtl (cw : Word) (c : Ctl) : Prop where
  hold : c.hold = none
  term : WTerm c.term
  body : PreSplit c.term → EnvBody cw c.env
  cj : ¬ PreSplit c.term → EnvCJ cw c.env

/-- The global context of the inversions below (any would do). -/
private def gW : G := { p := wakeSrc, k := Promises.Knobs.all, arch := .arm, n := 2, i := 1, lbase := 0 }

/-- The successor of a local step from the thread with the step's control. -/
private theorem localStep_eq {c c' : Ctl} (h : LocalStep wakeSrc c c') {th' : TTh}
    (ht : tstep gW #[] [] { term := c.term, env := c.env } = [(#[], [], th')]) :
    th'.term = c'.term ∧ th'.env = c'.env := by
  have := h.2 gW #[] [] { term := c.term, env := c.env } rfl rfl rfl rfl rfl
  rw [ht] at this
  simp only [List.cons.injEq, Prod.mk.injEq, and_true] at this
  rw [this.2.2]
  exact ⟨rfl, rfl⟩

/-- No local step from a thread whose `tstep` has no outcome. -/
private theorem localStep_nil {c c' : Ctl} (h : LocalStep wakeSrc c c')
    (ht : tstep gW #[] [] { term := c.term, env := c.env } = []) : False := by
  have := h.2 gW #[] [] { term := c.term, env := c.env } rfl rfl rfl rfl rfl
  rw [ht] at this
  cases this

/-- **No local step at the worker's store**: the store pushes a message. -/
theorem localStep_wkStore_false {cw : Word} {cS : WeakMem.Address} {c c' : Ctl} (h : LocalStep wakeSrc c c')
    (ht : c.term = wkStore) (hc : EnvCJ cw c.env) (hcw : cw.val = .loc cS 0) : False := by
  obtain ⟨⟨t, μ, u, hev, hcell, hu⟩, -⟩ := hc
  let th : TTh := { term := c.term, env := c.env }
  have hA : AtStore cw cS th := ⟨ht, rfl, rfl, ⟨t, μ, u, hev, hcell, hu⟩, hcw⟩
  obtain ⟨th1, hs, -⟩ := stepStore_append_mem gW.k gW.arch #[] (mth (stOf #[] [] th) cw one one) cS
    (dataE 1 one) [0] true
  have hm := atStore_tstep (g := gW) (pairs := []) hA hs
  rw [h.2 gW #[] [] th rfl rfl rfl rfl rfl] at hm
  simp only [List.mem_singleton, Prod.mk.injEq] at hm
  have := congrArg Array.size hm.1
  simp at this

/-- **No local step at `unpark`** (an extern). -/
theorem localStep_wkUnpark_false {c c' : Ctl} (h : LocalStep wakeSrc c c') (ht : c.term = wkUnpark) : False :=
  localStep_nil h (by simp [tstep, ht, wkUnpark, evalOp])

/-- **A local step at the worker's spawn** enters `worker`'s body. -/
theorem localStep_wkTail {cw : Word} {c c' : Ctl} (h : LocalStep wakeSrc c c') (ht : c.term = wkTail)
    (hb : EnvBody cw c.env) : ∃ jw, jw.val = mainTidW ∧ c'.term = wkBody ∧ c'.env = [("a", wkArgTy, [cw, jw])] := by
  obtain ⟨u, v, us, jw, hev, -, -, -, hj⟩ := hb
  obtain ⟨d, hd, ha, hty, hbd⟩ := wakeSrc_find_worker
  have e := tstep_tail (g := gW) (mem := #[]) (pairs := []) (th := { term := c.term, env := c.env })
    (by rw [ht]; rfl) rfl hd hev
  simp only [close_nil, ha, hty, hbd, List.reverse_nil] at e
  obtain ⟨e1, e2⟩ := localStep_eq h e
  exact ⟨jw, hj, e1.symm, e2.symm⟩

/-- **A local step at the worker's body** splits `a` into `c` and `j`. -/
theorem localStep_wkBody {cw : Word} {c c' : Ctl} (h : LocalStep wakeSrc c c') (ht : c.term = wkBody)
    (hb : EnvBody cw c.env) : c'.term = wkStore ∧ EnvCJ cw c'.env := by
  obtain ⟨u, v, us, jw, hev, hu, hn, ⟨μ, u', hcell, hu'⟩, hj⟩ := hb
  have hs := (localStepS_split (p := wakeSrc) (x := "c") (y := "j") (e := wkStore) (by rw [ht]; rfl) hev hu).2
    gW #[] [] { term := c.term, env := c.env } rfl rfl rfl rfl
  obtain ⟨e1, e2⟩ := localStep_eq h hs
  simp only at e1 e2
  refine ⟨e1.symm, ?_⟩
  rw [← e2, hn]
  refine ⟨⟨u, μ, u', ?_, hcell, hu'⟩, v, jw, ?_, hj⟩
  · simp [evalAt, lookupE]
  · simp [evalAt, lookupE]

/-- **A local step keeps the worker's control invariant**: from the spawn
to the body, from the body to the store; none elsewhere. -/
theorem localStep_wCtl {cw : Word} {cS : WeakMem.Address} (hcw : cw.val = .loc cS 0) {c c' : Ctl}
    (h : LocalStep wakeSrc c c') (hc : WCtl cw c) : WCtl cw c' := by
  rcases hc.term with ht | ht | ht | ht | ht
  · obtain ⟨jw, hj, e1, e2⟩ := localStep_wkTail h ht (hc.body (.inl ht))
    exact ⟨h.1, by rw [e1]; exact .inr (.inl rfl), fun _ => by rw [e2]; exact envBody_entry hj,
      fun hn => absurd (by rw [e1]; exact .inr rfl) hn⟩
  · obtain ⟨e1, hcj⟩ := localStep_wkBody h ht (hc.body (.inr ht))
    refine ⟨h.1, by rw [e1]; exact .inr (.inr (.inl rfl)), fun hp => ?_, fun _ => hcj⟩
    rw [e1] at hp
    rcases hp with hp | hp <;> simp [wkStore, wkTail, wkBody] at hp
  · have hn : ¬ PreSplit c.term := by
      rw [ht]; rintro (hp | hp) <;> simp [wkStore, wkTail, wkBody] at hp
    exact (localStep_wkStore_false h ht (hc.cj hn) hcw).elim
  · exact (localStep_wkUnpark_false h ht).elim
  · exact (localStep_not_ret h .unit ht).elim

/-- **A local run keeps the worker's control invariant.** -/
theorem localRun_wCtl {cw : Word} {cS : WeakMem.Address} (hcw : cw.val = .loc cS 0) {c c' : Ctl}
    (h : LocalRun wakeSrc c c') (hc : WCtl cw c) : WCtl cw c' := by
  induction h with
  | refl => exact hc
  | step hs _ ih => exact ih (localStep_wCtl hcw hs hc)

/-! ## Before the store -/

/-- **Before its store the worker runs locally to its store**: from a
control in `WCtl` before the store point, a local run (at any depth) to a
control at `wkStore` whose environment gives `c`'s word. -/
theorem localRunS_store {cw : Word} {c : Ctl} (hc : WCtl cw c) (hpre : c.term ≠ wkUnpark ∧ c.term ≠ .ret .unit) :
    ∃ env, LocalRunS wakeSrc c ⟨wkStore, env, none⟩ ∧ EnvCJ cw env := by
  have hbody : ∀ c0 : Ctl, c0.term = wkBody → EnvBody cw c0.env →
      ∃ env, LocalRunS wakeSrc c0 ⟨wkStore, env, none⟩ ∧ EnvCJ cw env := by
    intro c0 ht hb
    obtain ⟨u, v, us, jw, hev, hu, hn, ⟨μ, u', hcell, hu'⟩, hj⟩ := hb
    refine ⟨_, .single (localStepS_split (x := "c") (y := "j") (e := wkStore) (by rw [ht]; rfl) hev hu), ?_⟩
    rw [hn]
    exact ⟨⟨u, μ, u', by simp [evalAt, lookupE], hcell, hu'⟩, v, jw, by simp [evalAt, lookupE], hj⟩
  rcases hc.term with ht | ht | ht | ht | ht
  · obtain ⟨u, v, us, jw, hev, -, -, -, hj⟩ := hc.body (.inl ht)
    obtain ⟨d, hd, ha, hty, hbd⟩ := wakeSrc_find_worker
    have h1 := localStepS_tail (p := wakeSrc) (by rw [ht]; rfl) hd hev
    rw [ha, hty, hbd] at h1
    obtain ⟨env, h2, he⟩ := hbody ⟨wkBody, [("a", wkArgTy, [cw, jw])], none⟩ rfl (envBody_entry hj)
    exact ⟨env, .step h1 h2, he⟩
  · obtain ⟨env, h2, he⟩ := hbody c ht (hc.body (.inr ht))
    exact ⟨env, h2, he⟩
  · have hn : ¬ PreSplit c.term := by
      rw [ht]; rintro (hp | hp) <;> simp [wkStore, wkTail, wkBody] at hp
    refine ⟨c.env, ?_, hc.cj hn⟩
    have : c = ⟨wkStore, c.env, none⟩ := by
      obtain ⟨t, e, hh⟩ := c
      have h0 : hh = none := hc.hold
      simp only at ht ⊢; rw [ht, h0]
    rw [← this]; exact .refl _
  · exact absurd ht hpre.1
  · exact absurd ht hpre.2

/-- **A certificate before the store**: the worker in `WCtl` before its
store point, one frame, no type variables, its one promise `t` a message of
`c`'s `1` at a view covering the store's and above its ordering bound (the
local run to the store keeps the views), is certified. -/
theorem certified_pre {k : Promises.Knobs} {arch : WeakMem.Arch} {s : TermRun.Cfg} {th : TTh} {cw : Word}
    {cS : WeakMem.Address} {t w : Nat} (hi : s.ths[1]? = some th) (hc : WCtl cw (Ctl.of th))
    (hpre : th.term ≠ wkUnpark ∧ th.term ≠ .ret .unit) (hst : th.stack = []) (hσ : th.σs = [])
    (hcw : cw.val = .loc cS 0) (hp : th.promises = [t]) (hm : s.mem[t]? = some ⟨cS, .num 1, w⟩)
    (hmv : Promises.storeMview (wTh th.vs cw) (dataE 1 one) [0] true ≤ w)
    (hob : Promises.storeOb k arch (wTh th.vs cw) cS (dataE 1 one) [0] < t) :
    Certified wakeSrc k arch s 1 := by
  obtain ⟨env, hr, hcj⟩ := localRunS_store hc hpre
  have hsolo := localRunS_solo (k := k) (arch := arch) hr hi rfl rfl hσ
  let th' : TTh := { th with term := wkStore, env := env }
  have hi' : ({ s with ths := s.ths.set! 1 th' } : TermRun.Cfg).ths[1]? = some th' := getElem?_set!_self hi th'
  obtain ⟨⟨ty, μ, u, hev, hcell, hu⟩, -⟩ := hcj
  have hA : AtStore cw cS th' := ⟨rfl, hst, hσ, ⟨ty, μ, u, hev, hcell, hu⟩, hcw⟩
  exact certified_of_solo hsolo (certified_store (p := wakeSrc) hi' hA hp hm hmv hob)

/-- info: 'Spike.Lib.WakeW1.certified_pre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certified_pre

/-- info: 'Spike.Lib.WakeW1.localRun_wCtl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms localRun_wCtl

end Spike.Lib.WakeW1
