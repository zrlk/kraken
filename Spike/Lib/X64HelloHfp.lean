/-
**hello.w on x86-64: main's frame pointer at the clone** (the hello twin of `Spike/Lib/X64WakeHfp.lean`):
`X64HelloSegEnd.hpc_ofR`'s `hfp` (`fp = ⟨Rm.base, -128, 40⟩.addr 80` for the clone's `JS` node) from the clone's
mid state `X64HelloHMid.CloneMidH` at the pinned ghost `GJ1RH`, given `scc_rt_main`'s `%rbp` at `call wc_main`.

The clone's `JS` node and `CloneMidH`'s `wcNSH` node both address their frame from `%rbp` (`oP`, `oWH`: `%rbp` at
offset `0`), so their regions share the base and their slot `0` (`fp_uniqueH`). `wcNSH`'s slot `0` is `FrMGH`'s
saved `%rbp` `fr.1`, `wc_main`'s entry `%rbp` (`wcJ0 (mWC lab σC Jr)`), which `mWC` takes from the caller's state
`Jr σx` (`fp_of_frMGH`). With `scc_rt_main`'s `%rbp` at `(RS helloLsw v).addr (-8)` (`hpin`) and `GJ1RH`'s region
`(wcR (RS helloLsw v) helloD).fp (-8)` (base 88 below `RS`'s), `fp` is the base plus `80`.

- `fp_of_frMGH`: `FrMGH` at `wcJ0 (mWC lab σC Jr).J σ1` makes `fr.1` a caller's `%rbp` under `Jr`.
- `fp_uniqueH`: two abstractions of one machine state whose offsets both put `%rbp` at `0`, on regions holding
  offset `0`, share the base and slot `0`.
- `hfp_of_parts`: `hfp` at a `CloneMidH` state at `GJ1RH`, from the pin `hpin` at `GJ1RH`'s witnesses.
- `hfp_SegEnd`: `hpc_ofR`'s `hfp` at a level whose clone states are `CloneMidH` at `GJ1RH` with the pin.
- `hfp_W`: `hpc_ofR`'s `hfp` at `inv2 := inv2H`, from `X2H`'s frame-pointer clause (`X64HelloH2Inv.fp2_of`).

**Where this differs from AArch64** (forced by the x86-64 shape): AArch64's `MainSegH` has no frame pointer field
(any `x29`, `WakeMainFrames.frames_unit`), so it has no twin; x86-64's main reads its frame through `%rbp`, so
`MainSegH.hfp` pins `fp`. Against wake's `X64WakeHfp`:
- The pin is `scc_rt_main`'s `%rbp` under the caller's invariant `Jr` (`hpin`, stated per `GJ1RH` witness as
  `∀ σx c, Jr σx c → σx.regs.get64 .rbp = (RS helloLsw v).addr (-8)`), not `ClonePost`'s `%rsp` conjunct
  (wake's `hσC`, from `X64WakeBox.box_rsp`): hello's `ClonePostH`, `BoxPureH` and `GJ1H` carry no `%rbp` fact,
  and `wcF`'s `Abs` of `σC` is at `⟨-80, []⟩` (no `%rbp`). `hpin` is open in `hfp_of_parts`; `RootHP.hpin_RH`
  discharges it.
- Uniqueness goes through `%rbp` (`fp_uniqueH`; both nodes' offsets fix it) rather than `%rsp + 64` (wake's
  `fp_unique`); `slot_eq_of_abs` is wake's, reused.
- `fp_of_frG` becomes `fp_of_frMGH` (hello's `FrMGH` records `%rbp` itself, wake's `FrG` `%rsp + 40`).
- `hfp_of_clonePost` is not twinned (hello's `ClonePostH` has no pin). `hfp_W` reads the fact from `X2H`'s clone
  clause (`fp2_of`, put there by `hCP_of` from `CloneMidH` at `GJ1RH` and `hpin_RH`), not from `OPrem`'s
  `ClonePost` (wake's `hpostC_W`).
-/
import Spike.Lib.X64HelloSegEnd
import Spike.Lib.X64WakeHfp

namespace Spike.Lib.X64HelloHfp

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (pcOf)
open Spike.Lib (Region FragS Ctl)
open Spike.Lib.X64 (At Abs AS SO)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.Flow.Hello1 (mWC)
open Spike.Lib.X64.Flow.HelloM (wcR wcJ0)
open Spike.Lib.X64.Flow.HelloWc (FrMGH)
open Spike.Lib.X64.Flow.Worker.Hello.Parent (JS oP)
open Spike.Lib.X64.WakePh.MainGlue (RS)
open Spike.Lib.X64.HelloPh.StartH0G (helloLsw helloD)
open Spike.Lib.X64.HelloPh.RootHP (GJ1RH)
open Spike.Lib.X64HelloHMid (CloneMidH)
open Spike.Lib.X64HelloPreA (clonePcH cloneAtH)

/-- **`FrMGH`'s saved frame pointer is the caller's `%rbp`**: `wcJ0`'s `enter` keeps the registers, and `mWC`
takes `%rbp` from the caller's state under `Jr`. -/
theorem fp_of_frMGH {lab : Label → Int64} {σC σ1 : AS} {Jr : AS → Ctl → Prop} {fr : BitVec 64 × BitVec 64}
    {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {me : BitVec 64}
    (h : FrMGH (wcJ0 (mWC lab σC Jr).J σ1) fr sl me) :
    ∃ σx c, Jr σx c ∧ fr.1 = σx.regs.get64 .rbp := by
  obtain ⟨σe, c, ⟨rfl, σx, hJr, -, -, -, -, -, -, -, hbp, -⟩, rfl, -, -⟩ := h
  exact ⟨σx, c, hJr, by simp only [Spike.Lib.X64.enter, Reg64s.get64]; rw [hbp]⟩

/-- **Two `%rbp`-based abstractions of one machine state agree on the base and slot `0`**: both offsets put
`%rbp` at `0` (`SORel`), and both regions hold offset `0`. -/
theorem fp_uniqueH {R R' : Region} {o o' : SO} {m : MachineData} {σ σ' : AS} (h : Abs R o m σ)
    (h' : Abs R' o' m σ') (ho : o.get .rbp = some 0) (ho' : o'.get .rbp = some 0) (h0 : R.Off 0)
    (h0' : R'.Off 0) : R.base = R'.base ∧ σ.slot 0 = σ'.slot 0 := by
  have hb := h.so .rbp 0 ho
  have hb' := h'.so .rbp 0 ho'
  have er : σ.regs = σ'.regs := h.regs.symm.trans h'.regs
  have e : R.base = R'.base := by
    have hz : ∀ Q : Region, Q.addr 0 = Q.base := fun Q => by simp [Region.addr]
    rw [← hz R, ← hz R', ← hb, ← hb', er]
  refine ⟨e, ?_⟩
  obtain ⟨j, hj, hσ⟩ := h.slot 0 h0
  obtain ⟨j', hj', hσ'⟩ := h'.slot 0 h0'
  rw [show R.addr 0 = R'.addr 0 by simp [Region.addr, e], hj'] at hj
  cases hj
  rw [← hσ, ← hσ']

/-- **`hfp` at a clone mid state**: at `CloneMidH` at the pinned ghost `GJ1RH`, with `scc_rt_main`'s `%rbp` at
`(RS helloLsw v).addr (-8)` under the ghost's caller invariant `Jr` (`hpin`), every `JS` node of the clone at the
state over `⟨Rm.base, -128, 40⟩` has `fp = ⟨Rm.base, -128, 40⟩.addr 80`. -/
theorem hfp_of_parts {L : RuntimeLayout} {F0 : MachineData → Prop} {lbl1 : Spike.Lib.X64Consumer.Lbl}
    {lr : WeakMem.AllocLabel} {W : FragS isa} {Wc : Frag isa} {l : WeakMem.AllocLabel} {b n : Nat}
    {ws : List TermRun.Word} {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (h : CloneMidH L F0 (GJ1RH L lbl1 lr) W Wc l b ws n s c fs)
    (hpin : ∀ R F J1 t, GJ1RH L lbl1 lr R F J1 t → ∃ (σC σ1 : AS) (Jr : AS → Ctl → Prop) (v : BitVec 64),
      J1 = wcJ0 (mWC L.lab σC Jr).J σ1 ∧ R = (wcR (RS helloLsw v) helloD).fp (-8) ∧
      ∀ σx c, Jr σx c → σx.regs.get64 .rbp = (RS helloLsw v).addr (-8))
    {endPc' : Int64} {Rm : Region} {F₂ : MachineData → Prop} {cA fp ra tp : BitVec 64}
    (hat : At L.exe endPc' ⟨Rm.base, -128, 40⟩ F₂ ⟨cloneAtH L.exe, oP, JS c cA fp ra tp⟩ s c) :
    fp = (⟨Rm.base, -128, 40⟩ : Region).addr 80 := by
  obtain ⟨-, -, -, R, F, J1, t, sl, me, cA', fr, ⟨-, -, -, hRlo, hRhi, -⟩, hG, hFr, -, -, hAt, -, -⟩ := h
  obtain ⟨σC, σ1, Jr, v, rfl, rfl, hp⟩ := hpin _ _ _ _ hG
  obtain ⟨σx, c', hJr, hfr⟩ := fp_of_frMGH hFr
  obtain ⟨-, -, -, -, σ, hA, -, hJ⟩ := hAt
  obtain ⟨⟨⟨-, -, -, -, -, -, -, -, -, -, h0, -⟩, -⟩, -⟩ := hJ
  obtain ⟨-, -, -, -, σ', hA', -, -, -, h0', -⟩ := hat
  obtain ⟨e, hs⟩ := fp_uniqueH hA hA' rfl rfl ⟨by decide, by omega, by omega⟩
    ⟨rfl, show (-128 : Int) ≤ 0 by decide, show (0 : Int) + 8 ≤ 40 by decide⟩
  rw [← h0', ← hs, h0, hfr, hp σx c' hJr]
  show _ = Rm.base + _
  rw [← e]
  simp only [Region.addr, Spike.Lib.Region.fp, Region.callee, BitVec.add_assoc]
  rfl

/-- **`hpc_ofR`'s `hfp` at a level of clone mid states**: a level `inv2` whose clone states are `CloneMidH` at the
pinned ghost `GJ1RH` with the pin (`hmid`) has `hfp` there (`hfp_of_parts`). -/
theorem hfp_SegEnd {L : RuntimeLayout}
    {inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa}
    (hmid : ∀ l b n l' b' n' s c fs, inv2 l b n l' b' n' s c fs → pcOf s = clonePcH L →
      ∃ (F0 : MachineData → Prop) (lbl1 : Spike.Lib.X64Consumer.Lbl) (lr : WeakMem.AllocLabel) (W : FragS isa)
        (Wc : Frag isa) (l0 : WeakMem.AllocLabel) (b0 n0 : Nat) (ws : List TermRun.Word) (fs0 : List TermRun.Frame),
        CloneMidH L F0 (GJ1RH L lbl1 lr) W Wc l0 b0 ws n0 s c fs0 ∧
        ∀ R F J1 t, GJ1RH L lbl1 lr R F J1 t → ∃ (σC σ1 : AS) (Jr : AS → Ctl → Prop) (v : BitVec 64),
          J1 = wcJ0 (mWC L.lab σC Jr).J σ1 ∧ R = (wcR (RS helloLsw v) helloD).fp (-8) ∧
          ∀ σx c, Jr σx c → σx.regs.get64 .rbp = (RS helloLsw v).addr (-8)) :
    ∀ l b n l' b' n' s c fs, inv2 l b n l' b' n' s c fs → pcOf s = clonePcH L →
      ∀ (Rm : Region) (F₂ : MachineData → Prop) (cA fp ra tp : BitVec 64),
        At L.exe L.endPc ⟨Rm.base, -128, 40⟩ F₂ ⟨cloneAtH L.exe, oP, JS c cA fp ra tp⟩ s c →
        fp = (⟨Rm.base, -128, 40⟩ : Region).addr 80 := by
  intro l b n l' b' n' s c fs hi hpc Rm F₂ cA fp ra tp hat
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hm, hpin⟩ := hmid _ _ _ _ _ _ _ _ _ hi hpc
  exact hfp_of_parts hm hpin hat

/-- **`hpc_ofR`'s `hfp` at `inv2 := inv2H`** (wake's `hfp_W`): `X2H`'s clone clause carries the saved frame
pointer (`X64HelloH2Inv.fp2_of`), which `X64HelloH2CP.hCP_of` produces at the landing's `CloneMidH` states by
`hfp_of_parts` at `GJ1RH` with `RootHP.hpin_RH`. -/
theorem hfp_W {Dd : Spike.Lib.X64HelloO.ODataH} {L : RuntimeLayout}
    {W2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa}
    {K : State → State → Prop}
    {ms2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame →
      Spike.Lib.MemSide isa}
    {a : Int64} {ls0 : Spike.Lib.X64Consumer.Lsize}
    (hinv2 : Dd.inv2 = Spike.Lib.X64HelloH2Inv.inv2H W2 K ms2 L a L.endPc Dd.L0 ls0) :
    ∀ l b n l' b' n' s c fs, Dd.inv2 l b n l' b' n' s c fs → pcOf s = clonePcH L →
      ∀ (Rm : Region) (F₂ : MachineData → Prop) (cA fp ra tp : BitVec 64),
        At L.exe L.endPc ⟨Rm.base, -128, 40⟩ F₂ ⟨cloneAtH L.exe, oP, JS c cA fp ra tp⟩ s c →
        fp = (⟨Rm.base, -128, 40⟩ : Region).addr 80 := by
  intro l b n l' b' n' s c fs hi hpc
  rw [hinv2] at hi
  exact Spike.Lib.X64HelloH2Inv.fp2_of hi hpc

end Spike.Lib.X64HelloHfp

/-- info: 'Spike.Lib.X64HelloHfp.fp_of_frMGH' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64HelloHfp.fp_of_frMGH

/-- info: 'Spike.Lib.X64HelloHfp.fp_uniqueH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloHfp.fp_uniqueH

/-- info: 'Spike.Lib.X64HelloHfp.hfp_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloHfp.hfp_of_parts

/-- info: 'Spike.Lib.X64HelloHfp.hfp_SegEnd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloHfp.hfp_SegEnd

/-- info: 'Spike.Lib.X64HelloHfp.hfp_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloHfp.hfp_W
