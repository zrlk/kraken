/-
**main's read of the flag `c` under the two-thread relation** (main's half; `s1_threads.md` §2.2 option B). ISA-generic.

main's `waitLoop` reads `c` with an acquire load. Under the relation the
target read returns one of two values:

- a message at or before the spawn (`R.T`), which is main's latest
  pre-spawn write of `c` (main's coherence view covers every pre-spawn
  message to `cT`: `PreC.cov`), of value `0` (`PreC.val0`); or
- the worker's message `Tc` (`CProt.tmsg`), of value `1` (`CProt.some_msg`).

On the source side, once `c` is written (`oc = some (Tc, kc)`), `kc` is
the latest source message to `cS` (`CProt.smsg`: the only one after the
spawn), so a source load of `cS` can read it, whatever the reader's views.

`PreC` is part of main's per-thread relation (`PT 0`; the condition on proposal 2 of 1.4): it mentions only the memory up to the
spawn and main's coherence view of `cT`, so it is kept by every append
(`PreC.append`: a message of either thread, a promise) and by every step
of main that does not lower its coherence (`PreC.mono`). It holds at the
clone when the latest write of `cT` there has value `0` (`preC_start`).

- `PreC`: the coverage and value-`0` facts;
- `PreC.mono`, `PreC.append`, `preC_start`;
- `readSuccs_c`: a target read of `cT` by main returns a pre-spawn `0` or
  `Tc`'s `1`;
- `stepOne_load_c`: the same for one instruction that is a load of `cT`,
  with `PreC` kept and memory unchanged;
- `slatest_kc`, `stepLoad_kc`: the source load of `cS` reading `kc`.
-/
import Spike.Lib.HelloProt

namespace Spike.Lib.Inv2Read

open Kraken.Promising Kraken.Promising.Live.TicketStep Scc.Sem Spike.Lib.Inv2Core Spike.Lib.HelloProt

variable {I : ISA}

/-- **main's pre-spawn facts about `c`** (part of `PT 0`): main's coherence
view covers every target message to `cT` up to the spawn, and a read of
`cT` at a timestamp up to the spawn with no later pre-spawn message to
`cT` returns `0`. -/
structure PreC (R : SpawnRec) (cT : Loc) (tm : Memory) (vs : Views) : Prop where
  cov : ∀ k w, tm.get? k = some w → k ≤ R.T → w.loc = cT → k ≤ vs.getCoh cT
  val0 : ∀ t v, t ≤ R.T → tm.read? cT t = some v →
    (∀ k w, t < k → k ≤ R.T → tm.get? k = some w → w.loc ≠ cT) → v = 0

namespace PreC

variable {R : SpawnRec} {cT : Loc} {tm : Memory} {vs : Views}

/-- A coherence view of `cT` at least as high keeps `PreC`. -/
theorem mono (h : PreC R cT tm vs) {vs' : Views} (hle : vs.getCoh cT ≤ vs'.getCoh cT) : PreC R cT tm vs' :=
  ⟨fun k w hk hT hl => Nat.le_trans (h.cov k w hk hT hl) hle, h.val0⟩

/-- **An appended message keeps `PreC`** (the spawn is before it). -/
theorem append (h : PreC R cT tm vs) (hT : R.T ≤ tm.last) (w : Msg) : PreC R cT (tm.append w).1 vs := by
  refine ⟨fun k w' hk hk' hl => ?_, fun t v ht hr hno => ?_⟩
  · rw [Scc.Sem.Memory.get?_append_le (Nat.le_trans hk' hT)] at hk
    exact h.cov k w' hk hk' hl
  · rw [Scc.Sem.Memory.read?_append_le (Nat.le_trans ht hT)] at hr
    refine h.val0 t v ht hr fun k w' hk hk' hg => ?_
    rw [← Scc.Sem.Memory.get?_append_le (w := w) (Nat.le_trans hk' hT)] at hg
    exact hno k w' hk hk' hg

end PreC

/-- **`PreC` at the clone** (`R.T = tm.last`): from main's cover of every
message (`CohCoversP` with no promise, as `Inv1` gives) and a latest write
`j` of `cT` of value `0`. -/
theorem preC_start {R : SpawnRec} {cT : Loc} {tm : Memory} {vs : Views} (hT : R.T = tm.last)
    (hc : CohCoversP vs [] tm) {j : Nat} (hj : tm.read? cT j = some 0)
    (hjl : ∀ k w, j < k → tm.get? k = some w → w.loc ≠ cT) : PreC R cT tm vs := by
  refine ⟨fun k w hk _ hl => hl ▸ hc k w hk List.not_mem_nil, fun t v ht hr hno => ?_⟩
  have hjt : j = t := by
    rcases Nat.lt_trichotomy j t with hlt | heq | hgt
    · exfalso
      rcases Kraken.Promising.Memory.read?_eq_some tm hr with ⟨h0, -⟩ | ⟨w, hw, hl, -⟩
      · have h0' : t = 0 := h0
        omega
      · exact hjl t w hlt hw hl
    · exact heq
    · exfalso
      rcases Kraken.Promising.Memory.read?_eq_some tm hj with ⟨h0, -⟩ | ⟨w, hw, hl, -⟩
      · have h0' : j = 0 := h0
        omega
      · exact hno j w hgt (hT ▸ Kraken.Promising.Memory.le_last_of_get? hw) hw hl
  subst hjt
  rw [hj] at hr
  exact (Option.some.inj hr).symm

section Target

variable {R : SpawnRec} {C : CRec I} {oc : Option (Nat × Nat)} {tm : Memory} {t1 : Thread I}
  {sm : WeakMem.Memory} {s1 : TermRun.TTh} {ts : Nat → Option Nat} {tp sp : List Nat}

/-- **A target read of `cT` by main** returns a pre-spawn message, of value
`0`, or the worker's `Tc`, of value `1`. The context `c` is main's: its
coherence view of `cT` satisfies `PreC` over the memory. -/
theorem readSuccs_c (A : Arch) (iv : InstrViews) (hp : CProt R C oc tm t1 sm s1 ts tp sp) {c : Ctx}
    (hm : c.mem = tm) (hpre : PreC R C.cT tm c.views) {lk : Kraken.LoadKind} {xcl noRet : Bool} {x : Time × Val × Ctx}
    (hx : x ∈ readSuccs A iv c lk xcl C.cT noRet) :
    (x.1 ≤ R.T ∧ x.2.1 = 0) ∨ (∃ kc, oc = some (x.1, kc) ∧ x.2.1 = 1) := by
  obtain ⟨t, v, rfl, -, hv, hw, -⟩ := (mem_readSuccs A).mp hx
  rw [hm] at hv hw
  show (t ≤ R.T ∧ v = 0) ∨ (∃ kc, oc = some (t, kc) ∧ v = 1)
  by_cases htT : t ≤ R.T
  · refine .inl ⟨htT, hpre.val0 t v htT hv fun k w hk hk' hg hl => ?_⟩
    have hcov := hpre.cov k w hg hk' hl
    have : tm.writeIn C.cT t (max (readPre A iv c lk) (c.views.getCoh C.cT)) = true :=
      (Kraken.Promising.Memory.writeIn_iff _ _ _ _).mpr
        ⟨k, w, hk, Nat.le_trans hcov (Nat.le_max_right _ _), hg, hl⟩
    rw [hw] at this; cases this
  · have hT : R.T < t := Nat.lt_of_not_le htT
    rcases Kraken.Promising.Memory.read?_eq_some tm hv with ⟨h0, -⟩ | ⟨w, hg, hl, rfl⟩
    · have h0' : t = 0 := h0
      rw [h0'] at hT
      exact absurd hT (Nat.not_lt_zero _)
    · obtain ⟨kc, hoc, -⟩ := hp.tmsg t w hg hT hl
      obtain ⟨-, -, -, ⟨w', hg', -, -, hv'⟩, -⟩ := hp.some_msg t kc hoc
      rw [hg] at hg'
      cases hg'
      exact .inr ⟨kc, hoc, hv'⟩

/-- **One instruction of main that is a load of `cT`**: memory unchanged,
`PreC` kept, and the value read is a pre-spawn `0` or `Tc`'s `1`. -/
theorem stepOne_load_c (A : Arch) (hp : CProt R C oc tm t1 sm s1 ts tp sp) {t : Thread I} {tid : Nat}
    (hpre : PreC R C.cT tm t.views) {kl : Kraken.LoadKind} {xcl : Bool} {g : Val → I.State}
    (hex : I.exec t.st = some (.load kl xcl C.cT fun v => .done (g v)))
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid tm = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs) :
    o.mem = tm ∧ PreC R C.cT tm o.thread.views ∧
      ∃ v, o.thread.st = g v ∧ (v = 0 ∨ ∃ Tc kc, oc = some (Tc, kc) ∧ v = 1) := by
  obtain ⟨st, c', hr, hth, hm⟩ := (Lower.stepOne_ok_iff A tid hex).mp ⟨outs, o, hstep, ho, rfl, rfl⟩
  rw [Lower.run_load_iff] at hr
  obtain ⟨ts', v, hx, rfl⟩ := hr
  have hval := readSuccs_c A _ hp (c := ctx0 tid t tm) rfl hpre hx
  obtain ⟨v', -, -, hc'⟩ := readSuccs_shape A _ hx
  have hmem : c'.mem = tm := by have := congrArg Ctx.mem hc'; exact this
  obtain ⟨-, e2⟩ := finishInstr_relKey hth
  have e3 : o.thread.views.coh = c'.views.coh := by have := congrArg Views.coh e2; exact this
  have hle : t.views.getCoh C.cT ≤ o.thread.views.getCoh C.cT := by
    have h1 : t.views.getCoh C.cT ≤ c'.views.getCoh C.cT := by
      dsimp only at hc'
      rw [hc']; exact getCoh_le_setCoh _ _ _ _
    unfold Views.getCoh at h1 ⊢
    rw [e3]; exact h1
  refine ⟨hm.trans hmem, hpre.mono hle, v, finishInstr_st hth, ?_⟩
  rcases hval with ⟨-, h0⟩ | ⟨kc, hoc, h1⟩
  · exact .inl h0
  · exact .inr ⟨_, kc, hoc, h1⟩

end Target

section Source

variable {R : SpawnRec} {C : CRec I} {tm : Memory} {t1 : Thread I}
  {sm : WeakMem.Memory} {s1 : TermRun.TTh} {ts : Nat → Option Nat} {tp sp : List Nat}

/-- **`kc` is the latest source message to `cS`**: the only one after the
spawn. -/
theorem slatest_kc {Tc kc : Nat} (hp : CProt R C (some (Tc, kc)) tm t1 sm s1 ts tp sp) :
    MemRel.SLatest sm C.cS kc := by
  obtain ⟨-, hS, -, -, m, hm, hl, -⟩ := hp.some_msg Tc kc rfl
  refine ⟨⟨m, hm, hl⟩, fun k m' hk hk' hl' => ?_⟩
  obtain ⟨Tc', he⟩ := hp.smsg k m' hk' (Nat.le_trans hS (Nat.le_of_lt hk)) hl'
  cases he
  exact Nat.lt_irrefl _ hk

/-- **The source load of `cS` reading `kc`**: any source thread's load of
`cS` has an outcome whose destination holds `kc`'s value `1`, view and
timestamp. -/
theorem stepLoad_kc {Tc kc : Nat} (hp : CProt R C (some (Tc, kc)) tm t1 sm s1 ts tp sp) (arch : WeakMem.Arch)
    (pairs : List Nat) (th : Promises.Thread) (dst : WeakMem.Reg) (deps : List WeakMem.Reg) (acq : Bool) :
    ∃ m, sm[kc]? = some m ∧ m.val = .num 1 ∧
      ∃ th' ∈ Promises.stepLoad arch sm pairs th dst C.cS deps acq, th'.regs dst = ⟨m.val, m.view, kc⟩ := by
  obtain ⟨-, -, -, -, m, hm, -, hv⟩ := hp.some_msg Tc kc rfl
  exact ⟨m, hm, hv, stepLoad_latest arch pairs th dst deps acq (slatest_kc hp) hm⟩

end Source

end Spike.Lib.Inv2Read
