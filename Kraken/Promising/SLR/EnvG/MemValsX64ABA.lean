/-
**`treiber_aba_tagged.kl` never faults at the runner's declarations**
`x64_treiber_aba_tagged_runner_faultFree`,
program-level `Config.FaultFree` from the threads' start states under any
architecture (promises included).

The existing ABA development (`X64VecTreiberABA.lean`) proves the `.kl`'s
`~exists` clause but not fault-freedom: the node load `movq (%rax),%rbx` and
the push's store `movq %rax,(%r12)` go through pointers read from `head`.
Here both threads get **value specifications** (`MemValsX64.ValSpecX`) at
the declared layout `abaS` (`head` 16 bytes, `A` and `B` 8 bytes), with the
value invariant `AbaValL` / `AbaValV` (every location of `abaS` holds a
value with low quadword `0`, `A` or `B`; `MemValsX64ABARun.lean`).

Two departures from `x64_faultFree_of_valSpecs`:

- **Alignment.** `movdqa` and `lock cmpxchg16b` fault on an unaligned
  address (`gp_unaligned`), so the image is not statically fault-free
  (`DirsNoFaultCode`). It is fault-free wherever an environment runs it
  (`DirsNoFaultEnvX`, `MultiX64Align.lean`): an unaligned access has no
  environment answer (`abaImageV_noFaultEnv`). `noFault_valSpecD_env` and
  `x64_faultFree_of_valSpecs_env` are `noFault_valSpecD` /
  `x64_faultFree_of_valSpecs` with `DirsNoFaultEnvX`.
- **The private stack.** Each thread's start memory is its stack, split
  from `abaS` (`Split`), so `head`, `A` and `B` are off it.

Phase-1 limit: single-access trees (`abaImageV_phase1FX`).
-/
import Kraken.Promising.SLR.EnvG.MemValsX64ABARun
import Kraken.Promising.SLR.EnvG.MultiX64Align
import Kraken.Promising.SLR.EnvG.X64VecTreiberABA

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG

namespace Kraken.Promising.X64.EnvG

/-! The env twins `noFault_valSpecD_env` and `x64_faultFree_of_valSpecs_env`
moved (same names) to `MemValsX64.lean`, where the
`DirsNoFaultCode` forms are their instances. -/

end Kraken.Promising.X64.EnvG

namespace Kraken.Promising.X64.EnvG.VecABA

/-! ## No fault where the environment runs the image -/

/-- `lock cmpxchg16b`'s tree has no fault where an environment answers it:
unaligned, its effects are `gp_unaligned` (no answer); aligned, one `rmw16`
with `done` continuations. -/
theorem cas16_noFaultEnv {E : SharedEnv} {g : E.State} {P : MachineState → E.State → Prop}
    (r : Std.Rco Int64) (s : MachineData) (addr : BitVec 64) (op : BitVec 128 → Option (BitVec 128))
    (k : BitVec 128 → MachineData → Effects) (f : BitVec 128 → MachineData → MachineState)
    (hk : ∀ old s', k old s' = .done (f old s'))
    (X : Effects) (hstep : (Effects.require_exec_access r fun _ =>
      if isAligned 16 addr then X else .gp_unaligned addr 16).AllEnv E g P) :
    (toEv {} (Effects.require_exec_access r fun _ =>
      if isAligned 16 addr then s.rmw16K .acqRel addr op k else .gp_unaligned addr 16)).NoFault := by
  by_cases hal : isAligned 16 addr = true
  · simp only [toEv, hal, ↓reduceIte, MachineData.rmw16K]
    split
    · split <;> simp only [hk, Kraken.Promising.X64.toEv, EvTree.NoFault]
    · simp only [Kraken.Promising.X64.toEv, EvTree.access_empty, EvTree.NoFault, hk]
      intro _; trivial
  · simp [hal, Effects.AllEnv] at hstep

theorem abaCasL_noFaultEnv (S : SharedEnv.Layout) :
    ∀ d ∈ abaCasL, ∀ (e : _root_.Executable) z, DirNoFaultEnvX S e d z := by
  intro d hd e z E hF s pc g P1 P2 hstep
  simp only [abaCasL, List.mem_cons, List.not_mem_nil, or_false] at hd
  subst hd
  simp only [_root_.Directive.interp, _root_.Instr.interp, _root_.AvxOperation.interp, ↓reduceIte] at hstep ⊢
  rcases hstep with h | h
  · exact cas16_noFaultEnv _ _ _ _ _ _ (fun _ _ => rfl) _ h
  · exact cas16_noFaultEnv _ _ _ _ _ _ (fun _ _ => rfl) _ h

set_option maxHeartbeats 4000000 in
/-- The other directives: statically fault-free but the two `movdqa`s
(`gp_unaligned` unaligned: no answer) and the data cells (no step). -/
theorem abaDirsA_noFaultEnv (S : SharedEnv.Layout) :
    ∀ d ∈ abaDirsA, ∀ (e : _root_.Executable) z, DirNoFaultEnvX S e d z := by
  intro d hd e z E hF s pc g P1 P2 hstep
  simp only [abaDirsA, abaDataV, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hd
  repeat' (rcases hd with rfl | hd)
  all_goals simp [_root_.Directive.interp, _root_.Instr.interp, _root_.Operation.interp,
    _root_.AvxOperation.interp, _root_.AvxRegOrMem.interp, _root_.MachineData.setAvxLegacy,
    _root_.MachineData.loadAvx, _root_.MachineData.storeAvx,
    Kraken.Promising.X64.toEv, _root_.MachineData.load, _root_.MachineData.store,
    _root_.RegOrMem.interp, _root_.Operand.interp, _root_.MachineData.set]
  all_goals (repeat' (first | split | simp [Kraken.Promising.X64.toEv, Kraken.Promising.EvTree.NoFault,
        Kraken.Promising.EvTree.access_empty]))
  all_goals try simp [_root_.RelRegOrMem.interp, Kraken.Promising.X64.toEv, Kraken.Promising.EvTree.NoFault]
  all_goals first
    | (by_cases hz : s.status.zf = true <;> simp [hz, Kraken.Promising.X64.toEv, Kraken.Promising.EvTree.NoFault]; done)
    | (rename_i hna; simp [_root_.Directive.interp, _root_.Instr.interp, _root_.AvxOperation.interp,
        _root_.AvxRegOrMem.interp, _root_.MachineData.storeAvx, _root_.MachineData.loadAvx,
        _root_.MachineData.setAvxLegacy, hna, Effects.AllEnv] at hstep; done)
    | (simp [_root_.Directive.interp, Effects.AllEnv] at hstep; done)

/-- **The image is fault-free wherever an environment runs it**, at every
layout `S`. -/
theorem abaImageV_noFaultEnv [layout : _root_.Layout] (S : SharedEnv.Layout) :
    DirsNoFaultEnvX S (layout abaImageV) :=
  dirsNoFaultEnvX_layout fun d hd => by
    rcases List.mem_append.mp (abaImageV_sub_dirs d hd) with h | h
    · exact abaDirsA_noFaultEnv S d h
    · exact abaCasL_noFaultEnv S d h

variable [layout : _root_.Layout] [Executable.ValidLayout (layout abaImageV)]

/-! ## The specifications -/

omit [Executable.ValidLayout (layout abaImageV)] in
theorem abaS_le16 : Le16 abaS := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> simp

/-- The verbatim threads' value specifications at `abaS` (both end at
`done`). -/
noncomputable def abaValSpec : Nat → ValSpecX (AbaValL (symV "head") (symV "A") (symV "B")) (AbaValV (symV "A") (symV "B")) :=
  fun _ =>
    { S := abaS
      le16 := abaS_le16
      e := layout abaImageV
      valid := inferInstance
      endPc := labV "done"
      post := fun x => ∃ _ : Nat, (x.1.2 = labV "done" ∧ True) ∨ False
      post_end := fun _ h => h.elim fun _ h => h.elim And.left False.elim }

omit [Executable.ValidLayout (layout abaImageV)] in
/-- A start memory split from `abaS` keeps the nodes off the stack. -/
theorem stkV_of_split {ds : Decls} {lab : Label} {s : State} (h : StartV ds lab s) (hs : Split abaS s.st.1.dmem) :
    StkV (domS s) s.st.1 := by
  refine ⟨h.stk, fun h' => ?_, fun h' => ?_⟩
  · unfold domS at h'
    rw [hs (symV "A") ⟨symV "A", 8, by simp, by simp⟩] at h'; cases h'
  · unfold domS at h'
    rw [hs (symV "B") ⟨symV "B", 8, by simp, by simp⟩] at h'; cases h'

/-- **The value specifications hold at the start states with declarations.** -/
theorem abaValSpec_initD (hal : isAligned 16 (symV "head") = true) {ds : Decls} {s0 s1 : State}
    (h0 : StartV ds "p0" s0) (h1 : StartV ds "p1" s1) (hs0 : Split abaS s0.st.1.dmem)
    (hs1 : Split abaS s1.st.1.dmem) : ∀ tid s, [s0, s1][tid]? = some s → (abaValSpec tid).HoldsD ds s
  | 0, s, hs => by
    cases hs
    refine ⟨h0.exe, h0.endPc, h0.decls, hs0, ?_⟩
    rw [show s0.st = (s0.st.1, labV "p0") from Prod.ext rfl h0.pc]
    exact Safely.uncountEnv (p0V_memVals (domS s0) hal s0.st.1 ((), 0) (stkV_of_split h0 hs0))
  | 1, s, hs => by
    cases hs
    refine ⟨h1.exe, h1.endPc, h1.decls, hs1, ?_⟩
    rw [show s1.st = (s1.st.1, labV "p1") from Prod.ext rfl h1.pc]
    exact Safely.uncountEnv (p1V_memVals (domS s1) hal s1.st.1 ((), 0) (stkV_of_split h1 hs1))
  | _ + 2, _, hs => by cases hs

omit layout [Executable.ValidLayout (layout abaImageV)] in
/-- The initial memory of `Config.init` satisfies the value invariant when
`head = {A, 0}`, `A.next = B`, `B.next = 0` (`IV`; no messages yet). -/
theorem memVals_aba_init {P : Params} {states : List isa.State} {initMem : List (Loc × Val)}
    (hiv : IV P (Config.init states initMem).mem) :
    MemVals (AbaValL P.h P.a P.b) (AbaValV P.a P.b) (Config.init states initMem).mem := by
  obtain ⟨hH, hA, hB⟩ := hiv
  refine ⟨fun l hl => ?_, fun ts w hw _ => ?_⟩
  · rcases hl with rfl | rfl | rfl
    · show AbaPtr _ _ (lo _)
      rw [show (⟨P.h, 16⟩ : Loc) = P.hd from rfl, hH, lo_setWidth]
      exact .inr (.inl rfl)
    · show AbaPtr _ _ (lo _)
      rw [show (⟨P.a, 8⟩ : Loc) = nd P.a from rfl, hA, lo_setWidth]
      exact .inr (.inr rfl)
    · show AbaPtr _ _ (lo _)
      rw [show (⟨P.b, 8⟩ : Loc) = nd P.b from rfl, hB]
      exact .inl rfl
  · have hm : (Config.init states initMem).mem.msgs = #[] := rfl
    simp [Memory.get?, hm] at hw

/-! ## The theorem -/

/-- **No reachable configuration of the verbatim `treiber_aba_tagged.kl`
threads with the runner's declarations has a faulting step**, under any
architecture (promises included): for every valid layout of the image in
which `head` is 16-aligned, both threads run the image with strict sized
declarations `ds` agreeing on `abaS` (`head` 16 bytes, `A` and `B` 8
bytes), thread `0` from `p0` and thread `1` from `p1`, each on its private
stack (`StartV`) split from `abaS`, and the initial memory has
`head = {A, 0}`, `A.next = B`, `B.next = 0` (`IV`). -/
theorem x64_treiber_aba_tagged_runner_faultFree {A : Arch} {fuel : Nat} {ds : Decls} (hsz : ds.Sized)
    (hal : isAligned 16 (symV "head") = true) (hag : ds.AgreesOn abaS)
    {s0 s1 : isa.State} {initMem : List (Loc × Val)} (h0 : StartV ds "p0" s0) (h1 : StartV ds "p1" s1)
    (hs0 : Split abaS s0.st.1.dmem) (hs1 : Split abaS s1.st.1.dmem)
    (hiv : IV abaP (Config.init [s0, s1] initMem).mem) :
    Config.FaultFree A fuel (Config.init [s0, s1] initMem) :=
  x64_faultFree_of_valSpecs_env abaValSpec (fun _ => ds) (fun _ => hsz) (fun _ => hag)
    (fun _ => abaImageV_noFaultEnv _)
    (fun _ => rootOnlyD_of_phase1TreeFX abaImageV_phase1FX)
    (memVals_aba_init hiv) (init_threads_of (abaValSpec_initD hal h0 h1 hs0 hs1))

end Kraken.Promising.X64.EnvG.VecABA

#print axioms Kraken.Promising.X64.EnvG.VecABA.x64_treiber_aba_tagged_runner_faultFree
