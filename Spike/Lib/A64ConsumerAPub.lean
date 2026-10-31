/-
**The source's publication at a fence row, for the arena consumer**
(`MemSide.pub`, `Arena.pub`): an `Out` row under a memory side admitting
the source's publication is either the fence row with the publication
(`FenceRun.pub`: the source's `PubStep`, then a local run) or a row under
the same memory side with no publication. The source's publication step is
a thread step that changes the thread's views only (`fenceS _ .st`), so the
consumer's invariant (`PreJA`, which does not read the source's views) is
kept by it.

- `Out.unpubL`: an `Out` row is the fence row with the publication or one
  with no publication (`Out.unpub`, its `FenceRun.loc` case folded back).
- `src_publish_stepN`, `src_publish_step_cfgN`: the publication's `tstep`
  and thread step (memory, promises, stack, allocation count and box label
  kept).
- `src_publish_stepS`: the publication as a source step of thread 0.

`A64ConsumerA.instr_stepA` / `instr_stepAH` split their row at `Out.unpubL`:
the fence row with the publication lands in `PreJA` by the target's fence,
the source's publication step and its local run.
-/
import Spike.Lib.A64ConsumerAMem
import Spike.Lib.CtrRowsP

namespace Spike.Lib

open CoreLang CoreTerm
open Kraken.Promising

/-- **An `Out` row is the fence row with the source's publication, or one
with no publication**: a fence of kind `k` to `s'` where the memory side
admits the publication (`ms.pub`), the source's publication step `c → c₁`
then a local run to a control landing in `X`; or the same row under `ms`
with `pub := False` (a fence row whose run is local is one). -/
theorem Out.unpubL {I : ISA} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide I} {X : Frag I}
    {s : I.State} {c : Ctl} (h : Out p lbl ms X s c) :
    (∃ (k : Kraken.FenceKind) (s' : I.State) (c₁ c' : Ctl),
        I.exec s = some (.fence k fun _ => .done s') ∧ ms.pub ∧ PubStep k c c₁ ∧ LocalRun p c₁ c' ∧ X s' c') ∨
      Out p lbl { ms with pub := False } X s c := by
  rcases h.unpub with ⟨k, s', c', he, hr, hx⟩ | h
  · cases hr with
    | loc hr => exact .inr (.fence k s' c' he (.loc hr) hx)
    | pub hP hps hr => exact .inl ⟨k, s', _, c', he, hP, hps, hr, hx⟩
  · exact .inr h

namespace SrcMemN

open TermRun

/-- **The source's publication step** (`publish`, or `intoRgn`): the
thread at the `PubStep`'s landing, its views at the release fence, the
memory, promises, stack, allocation count and box label kept. -/
theorem src_publish_stepN (g : G) (mem : WeakMem.Memory) (pairs : List WeakMem.Ts) (th : TTh)
    {k : Kraken.FenceKind} {c c₁ : Ctl} (hps : PubStep k c c₁) (ht : th.term = c.term) (he : th.env = c.env) :
    ∃ th', (mem, pairs, th') ∈ tstep g mem pairs th ∧ th'.term = c₁.term ∧ th'.env = c₁.env ∧
      th'.promises = th.promises ∧ th'.σs = th.σs ∧ th'.stack = th.stack ∧ th'.nalloc = th.nalloc ∧
      th'.tidLbl = th.tidLbl := by
  obtain ⟨-, -, x, a, e, t, t', ws, hterm, hev, rfl⟩ := hps
  rw [← he] at hev
  rw [← ht] at hterm
  refine ⟨withS { th with term := e, env := (x, t', ws) :: th.env } (fenceS (stOf mem pairs th) .st), ?_,
    rfl, by simp [withS, he], rfl, rfl, rfl, rfl, rfl⟩
  rcases hterm with ⟨ht, hpt⟩ | ⟨r, ht, hrt⟩
  · rw [TermLocal.tstep_let_gen ht rfl]
    simp only [List.mem_map]
    refine ⟨(fenceS (stOf mem pairs th) .st, t', ws), ?_, rfl⟩
    simp only [evalOp, ol, hev, bind, Option.bind]
    unfold Spike.Lib.pubTy at hpt
    split at hpt <;> simp_all
  · rw [TermLocal.tstep_let_gen ht rfl]
    simp only [List.mem_map]
    refine ⟨(fenceS (stOf mem pairs th) .st, t', ws), ?_, rfl⟩
    simp only [evalOp, ol, hev, bind, Option.bind]
    unfold Spike.Lib.rgnTy at hrt
    split at hrt <;> simp_all

/-- `src_publish_stepN` as a thread step of thread `i`. -/
theorem src_publish_step_cfgN {p : Prog} {k0 : Promises.Knobs} {arch : WeakMem.Arch} {c : Cfg} {i : Nat}
    {th : TTh} (hi : c.ths[i]? = some th) {k : Kraken.FenceKind} {cc c₁ : Ctl}
    (hps : PubStep k cc c₁) (ht : th.term = cc.term) (he : th.env = cc.env) :
    ∃ th', { c with ths := c.ths.set! i th' } ∈ threadSteps p k0 arch c i ∧ th'.term = c₁.term ∧
      th'.env = c₁.env ∧ th'.promises = th.promises ∧ th'.σs = th.σs ∧ th'.stack = th.stack ∧
      th'.nalloc = th.nalloc ∧ th'.tidLbl = th.tidLbl := by
  obtain ⟨th', h, h1⟩ := src_publish_stepN (gOf p k0 arch c i) c.mem c.pairs th hps ht he
  exact ⟨th', SrcMem.mem_threadSteps hi h, h1⟩

end SrcMemN

/-- A control at a publication is at no `ret`. -/
theorem PubStep.not_ret {k : Kraken.FenceKind} {c c₁ : Ctl} (h : PubStep k c c₁) : ∀ a, c.term ≠ .ret a := by
  obtain ⟨-, -, x, a, e, t, t', ws, hterm, -, -⟩ := h
  intro a' h
  rcases hterm with ⟨ht, -⟩ | ⟨r, ht, -⟩ <;> rw [ht] at h <;> cases h

/-- A publication lands at no hold, at the next term and the extended
environment. -/
theorem PubStep.landing {k : Kraken.FenceKind} {c c₁ : Ctl} (h : PubStep k c c₁) :
    c.hold = none ∧ c₁ = ⟨c₁.term, c₁.env, none⟩ := by
  obtain ⟨-, hh, x, a, e, t, t', ws, -, -, rfl⟩ := h
  exact ⟨hh, rfl⟩

/-- A publication is no allocation. -/
theorem PubStep.notAlloc {k : Kraken.FenceKind} {c c₁ : Ctl} (h : PubStep k c c₁) :
    ∃ x o e, c.term = .let_ x o e ∧ (∀ a τ, o ≠ .newBuf a τ) ∧ ∀ a T, o ≠ .new a T := by
  obtain ⟨-, -, x, a, e, t, t', ws, hterm, -, -⟩ := h
  rcases hterm with ⟨ht, -⟩ | ⟨r, ht, -⟩
  · exact ⟨x, _, e, ht, fun _ _ h => (by cases h), fun _ _ h => (by cases h)⟩
  · exact ⟨x, _, e, ht, fun _ _ h => (by cases h), fun _ _ h => (by cases h)⟩

namespace A64ConsumerS

open Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64
open Scc.Sem.SrcSem (mainExit)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer

/-- **The source's publication as a step of thread 0** (`src_publish_step_cfgN`,
as `src_load_stepS`): the thread at the landing, its continuation off `ret`
at depth 0. -/
theorem src_publish_stepS {P : SrcSem.SrcParams} {p : Prog} (hP : HookOK P p) {c : TermRun.Cfg}
    {th : TermRun.TTh} {k : Kraken.FenceKind} {cc c₁ : Ctl} (h0 : c.ths[0]? = some th) (hp : th.promises = [])
    (hps : PubStep k cc c₁) (ht : th.term = cc.term) (he : th.env = cc.env)
    (hr : th.stack = [] → ∀ a, c₁.term ≠ .ret a) :
    ∃ th' : TermRun.TTh, (SrcSem.source P p).step 0 c [] { c with ths := c.ths.set! 0 th' } ∧
      th'.term = c₁.term ∧ th'.env = c₁.env ∧ th'.promises = [] ∧ th'.σs = th.σs ∧ th'.stack = th.stack ∧
      th'.nalloc = th.nalloc ∧ th'.tidLbl = th.tidLbl := by
  obtain ⟨th', hst, hte, hen, hp', hσ, hsk, hna, htl⟩ :=
    SrcMemN.src_publish_step_cfgN (p := p) (k0 := P.k) (arch := P.arch) h0 hps ht he
  have hlt : 0 < c.ths.size := (Array.getElem?_eq_some_iff.mp h0).1
  have h0' : ({ c with ths := c.ths.set! 0 th' } : TermRun.Cfg).ths[0]? = some th' := by simp [hlt]
  refine ⟨th', src_step_of_threadSteps hP hst h0' (hp'.trans hp)
    (mainExit_of_not_ret h0 fun a h => hps.not_ret a (ht ▸ h))
    (mainExit_of_pair h0' fun h a' => hte ▸ hr (hsk ▸ h) a'), hte, hen, hp'.trans hp, hσ, hsk, hna, htl⟩

end A64ConsumerS

/-- info: 'Spike.Lib.Out.unpubL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.Out.unpubL

/-- info: 'Spike.Lib.SrcMemN.src_publish_stepN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.SrcMemN.src_publish_stepN

/-- info: 'Spike.Lib.SrcMemN.src_publish_step_cfgN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.SrcMemN.src_publish_step_cfgN

/-- info: 'Spike.Lib.PubStep.not_ret' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.PubStep.not_ret

/-- info: 'Spike.Lib.PubStep.landing' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.PubStep.landing

/-- info: 'Spike.Lib.PubStep.notAlloc' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.PubStep.notAlloc

/-- info: 'Spike.Lib.A64ConsumerS.src_publish_stepS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64ConsumerS.src_publish_stepS

end Spike.Lib
