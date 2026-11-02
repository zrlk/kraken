/-
**The print phase's anchors and moves** (C4, relation half; data in
`Spike/Lib/X64HelloW1.lean`): the load anchor takes no local step, every
control of `print`'s loop runs locally to an anchor, and the print phase
is kept by `print`'s call and left by its return.

- `ldAnchor`: the load of byte `k`'s word is an anchor: a load takes no
  local step (in a memory whose one message at the word is `undef`, the
  read counts an undefined word, which a local step does not);
- `printCP_anchor`, `nextCP_anchor`, `laneCP_anchor`, `entry_anchor`: from
  the top of `printL` (`PrintCP`), after an `emit` (`nextCP`), at the lane
  (`laneCP`) and at `print`'s entry, a local run to an anchor;
- `printPh_wcP`: before the call, the source worker at the call is at
  `wcP` itself; `printPh_call`: `print`'s call
  (`X64HelloPrintSrcPub.callTh`) lands in the print phase; `printPh_pop`:
  `print`'s return lands in the store phase.

x86-64 twin of `Spike/Lib/HelloW1Anchor.lean` (same names, namespaces with the `X64` prefix).

Not twinned (unreachable from the AArch64 root `hello_linkedA`, so twins only
live constants): `laneCP_anchor`, `nextCP_anchor`, `printPh_pop`.
-/
import Spike.Lib.X64HelloW1
import Spike.Lib.Hello1RodataMem

namespace Spike.Lib.X64HelloW1

open CoreLang CoreTerm
open Spike.Lib
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.X64HelloSplit (envP wcP workerRestH workerCallH)
open Spike.Lib.X64HelloPrintSrcPub (PrintCP loadCP ldCP laneCP emitCP nextCP elemW printLPD_find)
open Spike.Lib.PrintSrc (printN printBody)
open Scc.Sem.MemRel (SLatest)
open Spike.Lib.X64WakeW1 (mainTidW)

/-! ## The load anchor -/

/-- **The load of byte `k`'s word is an anchor.** -/
theorem ldAnchor (pw wn : TermRun.Word) (l : WeakMem.AllocLabel) {n m k : Nat} (hk : k < printN n m) :
    PAnchor pw wn l n m (ldCP pw wn m k (elemW pw l (k / 8))) := by
  refine ⟨.inl ⟨k, hk, rfl⟩, fun a₁ h => ?_⟩
  let g : TermRun.G := { p := helloSrc, k := {}, arch := .arm, n := 1, i := 0, lbase := 0 }
  let mem : WeakMem.Memory := (#[] : WeakMem.Memory).push ⟨⟨l, k / 8⟩, .undef, 0⟩
  let c := ldCP pw wn m k (elemW pw l (k / 8))
  let th : TermRun.TTh := { term := c.term, env := c.env }
  have hj : SLatest mem ⟨l, k / 8⟩ 0 := Hello1RodataMem.SLatest_push_self #[] _ _ _
  have hm : mem[0]? = some ⟨⟨l, k / 8⟩, .undef, 0⟩ := rfl
  obtain ⟨vs, hl⟩ := SrcMem.loadUnits_one g.arch (elemW pw l (k / 8)) false (TermRun.stOf mem [] th) hj hm
  let th' : TermRun.TTh := { th with term := PrintSrc.printLane, vs := vs,
                                     env := ("wd", .lanes false .w8, [⟨.undef, 0, 0⟩]) :: th.env,
                                     undefs := th.undefs + TermRun.countUndef [⟨.undef, 0, 0⟩] }
  have ht : th.term = .let_ "wd" (.load false (.var "l")) PrintSrc.printLane := rfl
  have hel : TermRun.evalAt th.env (.var "l") = some (.loc .pub (.lanes false .w8), [elemW pw l (k / 8)]) := rfl
  have hpw' : (elemW pw l (k / 8)).val = .loc ⟨l, k / 8⟩ 0 := rfl
  have hmem : (mem, [], th') ∈ TermRun.tstep g mem [] th := by
    simp only [TermRun.tstep, ht, TermRun.evalOp, hel, cellOf, TermRun.addrOf, hpw', wordOf, TermRun.accs,
      List.mem_map]
    exact ⟨_, ⟨_, hl, rfl⟩, rfl⟩
  rw [h.2 g mem [] th rfl rfl rfl rfl] at hmem
  simp only [List.mem_singleton, Prod.mk.injEq] at hmem
  have := congrArg TermRun.TTh.undefs hmem.2.2
  simp [th', th, TermRun.countUndef] at this

/-! ## Local runs to an anchor -/

variable {pw wn : TermRun.Word} {l : WeakMem.AllocLabel} {n m : Nat}

/-- **From the top of `printL`**, at most `printN n m` bytes out: a local run
to the next load (through the element's `idx`) or to the return. -/
theorem printCP_anchor (hpw : pw.val = .loc ⟨l, 0⟩ 0) {k : Nat} {c : Ctl} (h : PrintCP pw wn n m k c)
    (hk : k ≤ printN n m) : ∃ a, LocalRunS helloSrc c a ∧ PAnchor pw wn l n m a := by
  rcases Nat.lt_or_eq_of_le hk with hk | rfl
  · exact ⟨_, (X64HelloPrintSrcPub.printCP_load printLPD_find h hk).trans
      (.single (X64HelloPrintSrcPub.printCP_idx hpw)), ldAnchor pw wn l hk⟩
  · obtain ⟨env, hr⟩ := X64HelloPrintSrcPub.printP_done_run (p := helloSrc) h
    exact ⟨_, hr, retAnchor rfl rfl⟩

/-- **At `print`'s entry** on a slice of `m ≠ 0` words: a local run to an
anchor. -/
theorem entry_anchor (hpw : pw.val = .loc ⟨l, 0⟩ 0) {wm : TermRun.Word} (hwm : wm.val = .num m) (hm0 : m ≠ 0)
    (hwn : wn.val = .num n) :
    ∃ a, LocalRunS helloSrc ⟨printBody, [("a", X64HelloRodataSrc.sliceTyP, [pw, wm, wn])], none⟩ a ∧
      PAnchor pw wn l n m a := by
  obtain ⟨a, hr, ha⟩ := printCP_anchor hpw (X64HelloPrintSrcPub.printCP_entry (n := n) hwn hm0) (Nat.zero_le _)
  exact ⟨a, (X64HelloPrintSrcPub.printP_entry_run printLPD_find hwm hm0).trans hr, ha⟩

/-! ## The call and the return -/

/-- No local step at the call of `print` (it pushes a frame). -/
theorem call_noStep {c c₁ : Ctl} (ht : c.term = workerCallH) (hs : LocalStepS helloSrc c c₁) : False := by
  have := hs.2 { p := helloSrc, k := {}, arch := .arm, n := 1, i := 0, lbase := 0 } #[] []
    { term := c.term, env := c.env } rfl rfl rfl rfl
  simp only [ht, workerCallH] at this
  cases hev : TermRun.evalAt c.env (.var "sl") <;>
    simp_all [TermRun.tstep, TermRun.callFrame, TermRun.enter, TermRun.ol, X64HelloPrintSrcPub.printPD_find]

/-- **Before the call, at the call**: in the print phase on an empty stack,
the source worker at `print`'s call is at `wcP` itself. -/
theorem printPh_wcP {cw : TermRun.Word} {s1 : TermRun.TTh} (h : PrintPh l n m cw s1) (hst : s1.stack = [])
    (ht : s1.term = workerCallH) :
    ∃ w0 w1 w2 w4 : TermRun.Word, w4.val = mainTidW ∧
      w0.val = .loc ⟨l, 0⟩ 0 ∧ w1.val = .num m ∧ m ≠ 0 ∧ w2.val = .num n ∧ s1.env = envP w0 w1 w2 cw w4 := by
  obtain ⟨w0, w1, w2, w4, hj, h0, h1, hm, h2, ⟨-, hr⟩ | ⟨hst', -⟩⟩ := h
  · refine ⟨w0, w1, w2, w4, hj, h0, h1, hm, h2, ?_⟩
    rcases localRunS_cases hr with he | ⟨c₁, hs⟩
    · exact congrArg Ctl.env he
    · exact (call_noStep ht hs).elim
  · rw [hst] at hst'
    cases hst'

/-- **`print`'s call keeps the print phase**: from the call (`wcP`, in the
print phase on an empty stack), the thread in `print`'s body on the
slice's words with the call's frame pushed (`X64HelloPrintSrcPub.callTh`). -/
theorem printPh_call {cw : TermRun.Word} {s1 : TermRun.TTh} (h : PrintPh l n m cw s1) (hst : s1.stack = [])
    (ht : s1.term = workerCallH) :
    ∃ w0 w1 w2 : TermRun.Word, TermRun.evalAt s1.env (.var "sl") = some (X64HelloRodataSrc.sliceTyP, [w0, w1, w2]) ∧
      PrintPh l n m cw (X64HelloPrintSrcPub.callTh s1 "u" workerRestH [w0, w1, w2]) := by
  obtain ⟨w0, w1, w2, w4, hj, h0, h1, hm, h2, he⟩ := printPh_wcP h hst ht
  refine ⟨w0, w1, w2, by rw [he]; rfl, w0, w1, w2, w4, hj, h0, h1, hm, h2, .inr ⟨?_, ?_⟩⟩
  · simp [X64HelloPrintSrcPub.callTh, hst, he, uFrame]
  · exact entry_anchor h0 h1 hm h2

/-- info: 'Spike.Lib.X64HelloW1.ldAnchor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ldAnchor

/-- info: 'Spike.Lib.X64HelloW1.printPh_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms printPh_call

end Spike.Lib.X64HelloW1

/-- info: 'Spike.Lib.X64HelloW1.printCP_anchor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloW1.printCP_anchor

/-- info: 'Spike.Lib.X64HelloW1.entry_anchor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloW1.entry_anchor

/-- info: 'Spike.Lib.X64HelloW1.call_noStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloW1.call_noStep

/-- info: 'Spike.Lib.X64HelloW1.printPh_wcP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloW1.printPh_wcP
