/-
Copied from x64's `Kraken/X64/Examples/AtomicsLink.lean`, adapted for AArch64:
the example is the compare-and-swap twin `cas_success` instead of x64's
`casIncr`.
-/
import Kraken.AArch64.Examples.WPAtomics
import Kraken.AArch64.EnvWPRules
import Kraken.AArch64.EnvVCGen
import Kraken.Promising.SeqLinkAArch64Prog
import Kraken.Promising.EnvWPAArch64

/-!
# `cas` at the machine, ready for the merged link

`cas_success` (Kraken/AArch64/Examples/WPAtomics.lean) is a `vcgen` triple.
`Program.instrStep_of_triple` reads it as the instruction-step judgment from
the start address of `cas`'s layout to its end address, without running
`vcgen` again (`cas_instrStep`), and `step1W_stop_of_end` gives the `hstop`
premise of `merged_link_halt` there (`cas_stop`). `cas_merged_halt` feeds the
three parts of `merged_premises_of_triple` to `merged_link_halt`, with the
access discipline (`hpres`/`hacc`/`h0`) left as hypotheses.

With the slot at `[x0]` shared:
`cas_correctEnv` is the same program as a `TripleEnv` in
`SharedEnv.lastWrite [([x0], 8)]`, the slot outside `dmem`. Both instructions
access the slot, so it is composed from the shared-location rules alone:
`cas_shared` for the `casal` (the compare succeeds, the environment state
takes `x2`) and `ldr_shared` for the `ldr` (it reads the environment state
back), with no memory-free instruction to lift through `wpEnv_of_triple`.
`env_link_halt` carries it to the Promising machine (`cas_promising`): every
halting promise-free run leaves `v` in `x1`, the initial `x2` in `x3` and as
the slot's last write, with no access-discipline premises
(`hpres`/`hacc`/`h0` are gone).

`cas_correctEnv'` is the same statement by `vcgen` over the environment wp
(`Kraken/AArch64/EnvVCGen.lean`): `cas_shared_spec` steps the `casal`, the
combined rule `ldr_env_spec` the `ldr`.
-/

open Std.WP
open Kraken
open Kraken.Promising
open Kraken.Promising.AArch64

section MachineWP

open MachineWP

variable [layout : _root_.Layout] [Executable.ValidLayout (layout cas)]

local instance cas.env' : CodeEnv := ⟨layout cas⟩

/-- `cas_success` as an instruction chain from the start address to the end
address of `cas`'s layout. -/
theorem cas_instrStep (d : MachineData) (v : UInt64)
    (h : Mem.loadInt d.dmem d.regs.X0.toBitVec 8 = some v.toBitVec.toInt)
    (h_eq : d.regs.X1 = v) :
    Eventually (layout cas).instrStep
      (fun st => st.2 = (layout cas).addrOf cas.length
        ∧ st.1.regs.X1 = v ∧ st.1.regs.X3 = d.regs.X2)
      (d, Kraken.Layout.start Directive) :=
  Program.instrStep_of_triple (cas_success d v h h_eq) rfl

/-- At the end address of `cas`'s layout every merged step stutters: the
`hstop` premise of `merged_link_halt`, for any layout of shared locations. -/
theorem cas_stop (L : SharedLayout) :
    ∀ y R, y.2 = (layout cas).addrOf cas.length → step1W L (layout cas) y R → R y :=
  step1W_stop_of_end L

/-- `cas_success` through the merged link: given the access discipline as an
invariant `Inv`, a promise-free run of the one-thread machine on `cas` from
the start address that reaches the end address ends in a state whose merge
has `x1 = v` and `x3` the initial `x2`. -/
theorem cas_merged_halt {L : SharedLayout} (hL : L.WF) (A : Arch) (fuel : Nat)
    {showPc : Int64 → String} {d : MachineData} {dpriv : DataMem} {mem : Memory} (v : UInt64)
    (h : Mem.loadInt d.dmem d.regs.X0.toBitVec 8 = some v.toBitVec.toInt)
    (h_eq : d.regs.X1 = v)
    (hm : mem.msgs = #[]) (hrel : MemRel L dpriv mem d.dmem) {Inv : MachineState → Prop}
    (hpres : ∀ s R, Inv s → step1 (layout cas) s R → step1 (layout cas) s (fun s' => R s' ∧ Inv s'))
    (hacc : ∀ s, Inv s → (Executable.step (layout cas) s .done).AllW L (fun _ => True))
    (h0 : Inv (d, Kraken.Layout.start Directive)) {c : Config isa}
    {endPc : Int64} (hE : (layout cas).addrOf cas.length = endPc)
    (hc : ReachablePF A fuel
      ⟨#[Thread.init ({ exe := layout cas, endPc, st := (⟨d.regs, d.status, dpriv⟩, Kraken.Layout.start Directive),
                        showPc } : State)], mem⟩ c)
    {t' : Thread isa} (ht : c.threads = #[t']) (hend : t'.st.st.2 = endPc) :
    ∃ D', MemRel L t'.st.st.1.dmem c.mem D' ∧
      t'.st.st.1.regs.X1 = v ∧ t'.st.st.1.regs.X3 = d.regs.X2 := by
  subst hE
  obtain ⟨hP, hstop, hev⟩ := merged_premises_of_triple (L := L) (cas_success d v h h_eq) rfl hpres hacc h0
  obtain ⟨D', hD', -, hpost⟩ := merged_link_halt hL A fuel hm hrel hP hstop hev hc ht hend
  exact ⟨D', hD', hpost⟩

omit [Executable.ValidLayout (layout cas)] in
/-- `cas` with the slot at `[x0]` shared: outside `dmem`, its value the
`lastWrite` environment state's. From slot value `v = x1`, the run ends with
`v` in `x1`, the initial `x2` in `x3` and in the slot. The `casal` is
`cas_shared` (the compare succeeds), the `ldr` is `ldr_shared`. -/
theorem cas_correctEnv (d : MachineData) (v : UInt64)
    (h_none : Mem.loadInt d.dmem d.regs.X0.toBitVec 8 = none) (h_eq : d.regs.X1 = v) :
    TripleEnv (SharedEnv.lastWrite [(d.regs.X0.toBitVec, 8)])
      (fun s g => s = d ∧ (g d.regs.X0.toBitVec).setWidth 64 = v.toBitVec)
      cas
      (fun s g => s.regs.X1 = v ∧ s.regs.X3 = d.regs.X2 ∧
        (g d.regs.X0.toBitVec).setWidth 64 = d.regs.X2.toBitVec)
      (fun _ _ _ => False) := by
  intro s g ⟨hs, hg⟩
  subst hs
  have hX0 : s.regs.getRegOrSp (RegOrSp.low (.reg .X0) .W64) = s.regs.X0.toBitVec := by simp
  have hX1 : s.regs.getRegOrZr (RegOrZr.low (.reg .X1) .W64) = v.toBitVec := by simp [h_eq]
  refine cas_shared _ .acqRel .W64 _ _ _ s g ⟨(fun h => nomatch h), ?_, ?_, ?_⟩
  · simpa using h_none
  · show (_, 8) ∈ [(_, 8)]
    simp
  · intro w g' ⟨hw, hg'⟩
    subst hw
    refine ldr_shared _ _ _ _ g' ⟨(fun h => nomatch h), fun rng => ?_⟩
    have hop : rmwOpBits MemWidth.W64.bits
        (fun old => if (old == BitVec.setWidth MemWidth.W64.bits (s.regs.getRegOrZr (RegOrZr.low (.reg .X1) .W64)))
          = true then some (BitVec.setWidth MemWidth.W64.bits (s.regs.getRegOrZr (RegOrZr.low (.reg .X2) .W64)))
          else none) (g (s.regs.getRegOrSp (RegOrSp.low (.reg .X0) .W64))) =
        some (s.regs.X2.toBitVec.setWidth 128) := by
      simp [rmwOpBits, hX0, hX1, hg]
    rw [hop] at hg'
    simp only at hg'
    simp only [AddrExpr.eval]
    refine ⟨?_, ?_, fun v₁ g₁ hs₁ => ?_⟩
    · simpa [BitVec.signed, ConstExpr.interp] using h_none
    · show (_, 8) ∈ [(_, 8)]
      simp [BitVec.signed, ConstExpr.interp]
    · obtain ⟨hv₁, hg₁⟩ := hs₁
      subst hg₁
      intro pc _
      refine .done _ (.inl ⟨rfl, ?_, ?_, ?_⟩)
      · simp [hX0, hg]
      · simp [hv₁, BitVec.signed, ConstExpr.interp, hg']
      · simp [hg']

set_option experimental.vcgen true in
omit [Executable.ValidLayout (layout cas)] in
/-- `cas_correctEnv` by `vcgen` on `⟨cas⟩ : EnvProgram _`, and the
verification conditions by `simp_all`. -/
theorem cas_correctEnv' (d : MachineData) (v : UInt64)
    (h_none : Mem.loadInt d.dmem d.regs.X0.toBitVec 8 = none) (h_eq : d.regs.X1 = v) :
    TripleEnv (SharedEnv.lastWrite [(d.regs.X0.toBitVec, 8)])
      (fun s g => s = d ∧ (g d.regs.X0.toBitVec).setWidth 64 = v.toBitVec)
      cas
      (fun s g => s.regs.X1 = v ∧ s.regs.X3 = d.regs.X2 ∧
        (g d.regs.X0.toBitVec).setWidth 64 = d.regs.X2.toBitVec)
      (fun _ _ _ => False) := by
  apply TripleEnv.of_triple
  unfold cas
  vcgen
  all_goals simp_all [SharedEnv.lastWrite, rmwOpBits, and_assoc, ← UInt64.toBitVec_inj]

omit layout [Executable.ValidLayout (layout cas)] in
/-- The layout of `cas`'s one shared location is well formed. -/
theorem cas_layout_wf (a : BitVec 64) : SharedLayout.WF [(a, 8)] where
  pos _ _ h := by rw [List.mem_singleton] at h; cases h; decide
  le16 _ _ h := by rw [List.mem_singleton] at h; cases h; decide
  disj _ _ _ _ _ ha hb _ _ := by
    rw [List.mem_singleton] at ha hb
    cases ha; cases hb
    exact ⟨rfl, rfl⟩

/-- **`cas` on the Promising machine.** A promise-free one-thread run of `cas`
from `d`, the slot at `[x0]` shared (no bytes in `dmem`, its value `v` in the
message-free memory `mem`) and `x1 = v`: when the thread has reached the end
of the text, `x1` is `v`, `x3` is the initial `x2`, and the slot's last write
is the initial `x2`. `cas_correctEnv` through `env_link_halt`; unlike
`cas_merged_halt`, no access-discipline premises (`hpres`/`hacc`/`h0`). -/
theorem cas_promising (A : Arch) (fuel : Nat) (showPc : Int64 → String) (d : MachineData) (v : UInt64)
    (mem : Memory) (hm : mem.msgs = #[])
    (hsplit : ∀ k, SharedLayout.Covers [(d.regs.X0.toBitVec, 8)] k → d.dmem.get? k = none)
    (h_eq : d.regs.X1 = v)
    (h_slot : (mem.finalVal (sharedLoc d.regs.X0.toBitVec 8)).setWidth 64 = v.toBitVec)
    (c : Config isa)
    (hc : ReachablePF A fuel ⟨#[Thread.init ({
      exe := layout cas
      endPc := (layout cas).addrOf cas.length
      st := (d, Kraken.Layout.start Directive)
      showPc := showPc } : State)], mem⟩ c)
    (t' : Thread isa) (ht : c.threads = #[t']) (hend : t'.st.st.2 = (layout cas).addrOf cas.length) :
    t'.st.st.1.regs.X1 = v ∧ t'.st.st.1.regs.X3 = d.regs.X2 ∧
      (c.mem.finalVal (sharedLoc d.regs.X0.toBitVec 8)).setWidth 64 = d.regs.X2.toBitVec := by
  have hnone : Mem.loadInt d.dmem d.regs.X0.toBitVec 8 = none := by
    cases hl : Mem.loadInt d.dmem d.regs.X0.toBitVec 8 with
    | none => rfl
    | some x =>
      have h0 := Mem.get?_isSome_of_loadBytes (Mem.loadBytes_isSome_of_loadInt hl) 0 (by decide)
      rw [hsplit _ ⟨_, 8, List.mem_singleton_self _, by simp⟩] at h0
      cases h0
  let g : BitVec 64 → BitVec 128 := fun _ => mem.finalVal (sharedLoc d.regs.X0.toBitVec 8)
  have henv : envRel [(d.regs.X0.toBitVec, 8)] g mem := by
    intro a n ha
    rw [List.mem_singleton] at ha
    cases ha
    rfl
  have hev := Program.instrStepEnv_of_tripleEnv (cas_correctEnv d v hnone h_eq) (s := d) (g := g)
    ⟨rfl, h_slot⟩
  obtain ⟨g', hrel', hP⟩ := env_link_halt _ (layout cas) (cas_layout_wf _) A fuel _ showPc d _ mem g _
    hm hsplit henv (fun x hx => hx.elim And.left False.elim) (cas_stop _) hev c hc t' ht hend
  obtain ⟨-, hx1, hx3, hslot⟩ := hP.resolve_right id
  refine ⟨hx1, hx3, ?_⟩
  have := hrel' _ 8 (List.mem_singleton_self _)
  rw [← hslot]
  exact this.symm

end MachineWP
