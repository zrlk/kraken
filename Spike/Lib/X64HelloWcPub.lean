/-
**hello.w's `wc_main` from `.x25` to its `clone`'s `syscall`, publishing the box at the `mfence`** (x86-64; no
AArch64 file corresponds: the hello counterpart of wake's `Spike/Lib/X64WakeWcPub.lean`).
`X64HelloWcSp6Seg.hello_wc_sp6_segW`'s segment, but with the source, at `boxTermH` (`let c = publish o in …`, `o`
bound to the box's owned locative, no hold) up to the fence, taking its publication step at `wc_main`'s `mfence`
(`.x25 + 44`, `Out.fence .sy`, `FenceRun.pub` under `ms.pub`) and standing at the published control from there to the
`syscall`.

hello's x86-64 listing has no fence at the source's `publish` position: scc's `# fence st` emits no code on x86-64,
whose stores are ordered. So the publication moves from there to the `mfence` before the clone, a stronger fence
(`.sy`, which `PubStep` admits) later in the same thread, past the reserve, `scc_rt_alloc_tcb`, the tid store and
`scc_rt_thread_init`. Until that fence the source stands at `boxTermH`: every segment from the box's store to `.x25`
is parametric in the source control.

- `MidPGH`: the source `c0` at `Q l A` for the box's word `cA = A`, at `boxTermH`, `o` bound to `l`'s owned
  locative at `ty` (wake's `MidPG`);
- `boxPubSyH`: the publication step at `boxTermH` under a full fence (wake's `boxPubSy`);
- `pNH`, `WcSp6PW`: the nodes, at `c0` up to the fence and at `c1` past it; their states inside `W`;
  `WcSp6PW.triv`;
- `hello_wc_sp6_pub_segW`: the segment from `.x25` to `wcNSH` at `c1`, given the publication step from `c0` to
  `c1` (`boxPubSyH` at `c1 = boxPubCtlH c0 ty l`).

## Differences from the AArch64 version

- AArch64's hello publishes at the `dmb ishst` past the box's store (`HelloWcMid`'s `hfr`, the source's `S`); here
  the publication is at `.x25`'s `mfence`, as in wake's x86-64 `X64WakeWcPub`.
- `WcSp6PW` takes the published control `c1` as a parameter (wake's `WcClonePW` takes `ty`, `l` and builds
  `boxPubCtl c0 ty l`); the users instantiate `c1 := boxPubCtlH c0 ty l`.
-/
import Spike.Lib.X64HelloWcSp6Seg
import Spike.Lib.X64HelloMainPreSrc

namespace Spike.Lib.X64.HelloPh.WcSp6

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.WakePh.WcClone (nrB mfence_ndW)
open Spike.Lib.X64HelloMainPreSrc (boxTermH boxPubCtlH)
open Scc.Cert.Rt.X64 (Lays endOf blockAt codeAt_blockAt_lays)
open SccCode (helloCells)

/-- **The box's source facts before the publication** (wake's `MidPG`): `c0` at `Q l A` for the box's word
`cA = A`, at `boxTermH` with no hold, `o` bound to `l`'s owned locative at `ty`. -/
def MidPGH (Q : WeakMem.AllocLabel → Nat → Ctl → Prop) (c0 : Ctl) (ty : Ty) (l : WeakMem.AllocLabel)
    (cA : BitVec 64) : Prop :=
  Q l cA.toNat c0 ∧ c0.term = boxTermH ∧ c0.hold = none ∧
    TermRun.evalAt c0.env (.var "o") = some (.ptr .own ty, [TermRun.cst (.loc ⟨l, 0⟩ 0)])

/-- `MidPGH` is inhabited: the control at `boxTermH` binding only `o` to `l`'s owned locative, at the guard
`Q := fun _ _ _ => True`. -/
example (l : WeakMem.AllocLabel) (ty : Ty) :
    MidPGH (fun _ _ _ => True) ⟨boxTermH, [("o", .ptr .own ty, [TermRun.cst (.loc ⟨l, 0⟩ 0)])], none⟩ ty l 0#64 :=
  ⟨trivial, rfl, rfl, by simp [TermRun.evalAt, TermRun.lookupE]⟩

/-- **The publication step at `boxTermH` under a full fence** (`PubStep .sy`): `o` bound to the box's owned
locative, no hold. -/
theorem boxPubSyH {c : Ctl} {ty : Ty} {l : WeakMem.AllocLabel} (ht : c.term = boxTermH) (hh : c.hold = none)
    (ho : TermRun.evalAt c.env (.var "o") = some (.ptr .own ty, [TermRun.cst (.loc ⟨l, 0⟩ 0)])) :
    PubStep .sy c (boxPubCtlH c ty l) :=
  ⟨.inr rfl, hh, "c", .var "o", _, .ptr .own ty, .ptr .pub ty, _, .inl ⟨ht, rfl⟩, ho, rfl⟩

/-- **The nodes from `.x25` to the `syscall`**: the source at `c0` up to the fence, at `c1` past it. -/
def pNH (lab : Label → Int64) (c0 c1 : Ctl) (t k : BitVec 64) (sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64)
    (me cA : BitVec 64) (fr : BitVec 64 × BitVec 64) : XS → ND
  | .n6 => wcN6H lab c0 t k sl me cA fr
  | .n6f => wcN6fH lab c0 t k sl me cA fr
  | .n6a => wcN6aH lab c1 t k sl me cA fr
  | .nd => wcNdH lab c1 t k sl me cA fr
  | .n10 => wcN10H lab c1 t k sl me cA fr
  | .nr => wcNrH lab c1 t k sl me cA fr

/-- **`.x25`'s states to the `syscall` inside `W`**, none moved by `K`, the source at `c0` up to the fence and
at `c1` past it. -/
structure WcSp6PW (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (c0 c1 : Ctl) (t k : BitVec 64)
    (sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) (me cA : BitVec 64) (fr : BitVec 64 × BitVec 64) :
    Prop where
  n6 : BlkW W K exe endPc R F (wcN6H (_root_.Executable.labels exe).label c0 t k sl me cA fr) sp6AH
  n6f : NodeW W K exe endPc R F (wcN6fH (_root_.Executable.labels exe).label c0 t k sl me cA fr)
  n6a : BlkW W K exe endPc R F (wcN6aH (_root_.Executable.labels exe).label c1 t k sl me cA fr) cloneLdH
  nd : NodeW W K exe endPc R F (wcNdH (_root_.Executable.labels exe).label c1 t k sl me cA fr)
  n10 : NodeW W K exe endPc R F (wcN10H (_root_.Executable.labels exe).label c1 t k sl me cA fr)
  nr : BlkW W K exe endPc R F (wcNrH (_root_.Executable.labels exe).label c1 t k sl me cA fr) nrB

/-- From `.x25` to the `syscall` inside the trivial predicate, with no outside moves. -/
theorem WcSp6PW.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {c0 c1 : Ctl} {t k : BitVec 64} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {me cA : BitVec 64}
    {fr : BitVec 64 × BitVec 64} :
    WcSp6PW (fun _ _ => True) (fun _ _ => False) exe endPc R F c0 c1 t k sl me cA fr :=
  ⟨BlkW.triv, NodeW.triv, BlkW.triv, NodeW.triv, NodeW.triv, BlkW.triv⟩

section Seg

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wc_main` from `.x25` to its `clone`'s `syscall`, publishing the box at the `mfence`**, inside `W` in any
valid layout of `helloCells`: from `wcN6H` with the source at `c0` to `wcNSH` with the source at `c1`, given the
publication step from `c0` to `c1` (`hpub`, `boxPubSyH`) under a memory side admitting it (`hP`). -/
theorem hello_wc_sp6_pub_segW {W : Frag isa} {K : State → State → Prop}
    {kp : Nat} (hp : Lays exe helloCells kp) (hend : endPc = endOf exe helloCells kp)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -128) (hhi : 16 ≤ R.hi)
    {c0 c1 : Ctl} {t k : BitVec 64} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {me cA : BitVec 64}
    {fr : BitVec 64 × BitVec 64} (hpub : PubStep .sy c0 c1) (hP : ms.pub)
    (hW : WcSp6PW W K exe endPc R F c0 c1 t k sl me cA fr) :
    SegW W K p lbl ms (At exe endPc R F (wcN6H (_root_.Executable.labels exe).label c0 t k sl me cA fr))
      (At exe endPc R F (wcNSH (_root_.Executable.labels exe).label c1 t k sl me cA fr)) := by
  have hin := hello_wcSp6InH
  simp only [wcSp6InH, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨b0, bf⟩, bl⟩, bd⟩, b10⟩, br⟩, -⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  have code : ∀ {k off : Nat} {b : List (Directive × Nat)}, blockAt helloCells x25L k off b = true →
      ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (lab x25L + Int64.ofNat off) b :=
    fun h s he hn => codeAt_blockAt_lays hp he (hn.trans hend) h
  have hB : SegW W K p lbl ms (At exe endPc R F (pNH lab c0 c1 t k sl me cA fr .n6))
      (fun s c => ∃ x : Unit, At exe endPc R F ((fun _ => wcNSH lab c1 t k sl me cA fr) x) s c) := by
    refine fn_segW (N := pNH lab c0 c1 t k sl me cA fr) (fun i => ?_) XS.n6
    cases i
    case n6 =>
      refine seg_ndW (by simp [sp6AH]) sp6AH_ok hF hR hlo hhi
        (fun s he hn => (by simpa using code b0 s he hn : CodeAt s (lab x25L) sp6AH)) hW.n6
        fun σ c hJ => ⟨c, .refl c, .inl ⟨XS.n6f, sp6AH_edge hJ⟩⟩
    case n6f =>
      refine mfence_ndW (fun s he hn => code bf s he hn) hW.n6f fun σ c hJ => ?_
      obtain ⟨hc, hA⟩ := hJ
      refine ⟨c1, .pub hP (by rw [hc]; exact hpub) (.refl _), .inl ⟨XS.n6a, ?_, rfl, rfl, hA⟩⟩
      show lab x25L + 47 = lab x25L + Int64.ofNat 44 + Int64.ofNat 3
      rw [Int64.add_assoc]; rfl
    case n6a =>
      exact seg_ndW (by simp [cloneLdH]) cloneLdH_ok hF hR hlo hhi (fun s he hn => code bl s he hn) hW.n6a
        fun σ c hJ => ⟨c, .refl c, .inl ⟨XS.nd, cloneLdH_edge hJ⟩⟩
    case nd =>
      refine flag_ndW (fi := .xor_rr32_self .rdx) rfl hF (fun s he hn => code bd s he hn) hW.nd
        fun σ c hJ fl => ⟨c, .refl c, .inl ⟨XS.n10, ?_, rfl, ?_, ?_⟩⟩
      · show lab x25L + 86 = lab x25L + Int64.ofNat 84 + Int64.ofNat 2
        rw [Int64.add_assoc]; rfl
      · obtain ⟨hA, h12, hbx, h13, h14, h15, h9, hsi, h8, hdi⟩ := hJ
        exact ⟨hA, by
          simp (disch := decide) only [FI.step, FI.regs, Reg64s.get64_set64_ne, h12, hbx, h13, h14, h15, h9,
            hsi, h8, hdi, and_self]⟩
      · simp only [FI.step, FI.regs, Reg64s.get64_set64_self]; rfl
    case n10 =>
      refine flag_ndW (fi := .xor_rr32_self .r10) rfl hF (fun s he hn => code b10 s he hn) hW.n10
        fun σ c hJ fl => ⟨c, .refl c, .inl ⟨XS.nr, ?_, rfl, ?_, ?_, ?_⟩⟩
      · show lab x25L + 89 = lab x25L + Int64.ofNat 86 + Int64.ofNat 3
        rw [Int64.add_assoc]; rfl
      · obtain ⟨⟨hA, h12, hbx, h13, h14, h15, h9, hsi, h8, hdi⟩, -⟩ := hJ
        exact ⟨hA, by
          simp (disch := decide) only [FI.step, FI.regs, Reg64s.get64_set64_ne, h12, hbx, h13, h14, h15, h9,
            hsi, h8, hdi, and_self]⟩
      · simp (disch := decide) only [FI.step, FI.regs, Reg64s.get64_set64_ne, hJ.2]
      · simp only [FI.step, FI.regs, Reg64s.get64_set64_self]; rfl
    case nr =>
      exact seg_ndW (by simp [nrB]) nrBH_ok hF hR hlo hhi (fun s he hn => code br s he hn) hW.nr
        fun σ c hJ => ⟨c, .refl c, .inr ⟨(), nrBH_edge hJ⟩⟩
  exact hB.mono_post fun _ _ ⟨_, h⟩ => h

end Seg

end Spike.Lib.X64.HelloPh.WcSp6

/-- info: 'Spike.Lib.X64.HelloPh.WcSp6.boxPubSyH' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcSp6.boxPubSyH

/-- info: 'Spike.Lib.X64.HelloPh.WcSp6.WcSp6PW.triv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcSp6.WcSp6PW.triv

/-- info: 'Spike.Lib.X64.HelloPh.WcSp6.hello_wc_sp6_pub_segW' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcSp6.hello_wc_sp6_pub_segW
