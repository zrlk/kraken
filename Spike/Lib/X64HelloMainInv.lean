/-
**hello.w: main's side after the spawn (x86-64)** (the twin of
`X64WakeInst.mainInv`, `mainWR`, `wakeM`): main's invariant over the source
program `p` (wake's `mainInv` fixes `wakeSrc`), its state predicate with the
flag load's pc in hello's `wc_waitLoop`, and main's `MSide` at `helloSrc`, over
any record type `ι` (the instance's) with its placement, memory side and
pointer word.

- `mainInvP p lbl ms W`: the union of the invariants closed under main's
  rows of `p` inside `W`; `mainInvP_closed`, `mainInvP_W`, `mainInvP_of`.
- `mainWRH lab exe Λ lbl lsize`: `X64WakeInst.mainWR` with the flag load's pc
  `lab ".Lwc_waitLoop.entry" + 7`.
- `helloM lbl lsize ms cw lab exe Λ μT hoff`: main's `MSide` (`p := helloSrc`,
  `Mi := mainInvP helloSrc … (mainWRH …)`, `off` from `hoff`, `wl` by
  `X64HelloB7b.hello_wl`).
- `hoff_ofPlaceW`: `hoff` at a placed output's runtime layout and marks
  (`X64AbOffL.off_of_A_ofPlaceOK`), so `helloM`'s `off` holds at hello's
  placed layout with no further premise.

## Differences from the AArch64 version

- Fragments are over `X64.isa`; the side is `X64WakeM0.MSide`, the placed
  output is a `PlaceWX` and the runtime layout `RuntimeLayout.ofPlaceWX`.
- x86-64 local labels carry no numbering prefix, so hello's flag-load pc
  `lab ".Lwc_waitLoop.entry" + 7` (the `movq -8(%rbp), %rcx` at `entry`, 4
  bytes, then the load's 3; the AArch64 version adds `4 + 4` to the prefixed
  `.L21_wc_waitLoop.0_entry`) is spelled exactly as wake's: `mainWRH` is
  `X64WakeInst.mainWR` by `rfl` (checked below).
- Not twinned (unreachable from the AArch64 root, so twins only live
  constants): `mainInvP_wake`.
-/
import Spike.Lib.X64WakeInst
import Spike.Lib.X64HelloB7b

namespace Spike.Lib.X64HelloMainInv

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib Spike.Lib.X64WakeA64
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.X64WakeInst (mainW)
open Spike.Lib.X64.Rt (RuntimeLayout)

/-- **The union of the invariants closed under main's rows of `p` inside
`W`** (`X64WakeInst.mainInv` at `wakeSrc`). -/
def mainInvP (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (ms : MemSide isa) (W : Frag isa) :
    Frag isa :=
  fun s c => ∃ inv : Frag isa, (∀ s c, inv s c → OutL p lbl ms inv s c) ∧
    (∀ s c, inv s c → W s c) ∧ inv s c

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa} {W : Frag isa}

theorem mainInvP_closed : ∀ s c, mainInvP p lbl ms W s c → OutL p lbl ms (mainInvP p lbl ms W) s c := by
  rintro s c ⟨inv, hcl, hW, hi⟩
  exact (hcl s c hi).mono fun s c h => ⟨inv, hcl, hW, h⟩

theorem mainInvP_W : ∀ s c, mainInvP p lbl ms W s c → W s c :=
  fun s c ⟨_, _, hW, hi⟩ => hW s c hi

/-- A state of an invariant closed under the rows inside `W` is in
`mainInvP`. -/
theorem mainInvP_of {inv : Frag isa} (hW : ∀ s c, inv s c → W s c)
    (hcl : ∀ s c, inv s c → OutL p lbl ms inv s c) {s : isa.State} {c : Ctl} (h : inv s c) :
    mainInvP p lbl ms W s c :=
  ⟨inv, hcl, hW, h⟩

/-- **main's state predicate after the spawn** at hello.w's listing:
`X64WakeInst.mainWR` with the flag load's pc in `wc_waitLoop` (`entry`, plus
the first `movq`'s 4 bytes and the load's 3). -/
def mainWRH (lab : String → Int64) (exe : _root_.Executable) (Λ : Scc.Sem.Layout)
    (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat) : Frag isa :=
  fun s c => mainW lab exe Λ lbl s c ∧ Spike.Lib.X64.RelWS s ∧
    Spike.Lib.X64WakeMappedRow.LabMapped lbl (Spike.Lib.X64Consumer.K0 Λ) c ∧
    Spike.Lib.X64WakeMainS.MainSys s ∧
    Spike.Lib.X64WakeMainF.FlagW lbl lsize (lab ".Lwc_waitLoop.entry" + Int64.ofNat 7) s c

/-- hello's flag-load pc is wake's: x86-64 labels carry no numbering prefix. -/
example : mainWRH = Spike.Lib.X64WakeInst.mainWR := rfl

/-- **main's side at hello.w** (see the module doc). -/
def helloM {ι : Type} (lbl : ι → WeakMem.AllocLabel → Option Nat) (lsize : ι → WeakMem.AllocLabel → Nat)
    (ms : ι → MemSide isa) (cw : ι → TermRun.Word) (lab : String → Int64) (exe : _root_.Executable)
    (Λ : Scc.Sem.Layout) (μT : Marks)
    (hoff : ∀ s c, Spike.Lib.X64WakeOff.AbOffA lab s c → ∀ k a, μT.abortAt k = some a → pcOf s ≠ a) :
    X64WakeM0.MSide ι where
  p := helloSrc
  lbl := lbl
  ms := ms
  Mi w := mainInvP helloSrc (lbl w) (ms w) (mainWRH lab exe Λ (lbl w) (lsize w))
  closed _ := mainInvP_closed
  cw := cw
  μ := μT
  off _ s c h := hoff s c (mainInvP_W s c h).1.1
  wl := X64HelloB7b.hello_wl

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- **`helloM`'s `hoff` at a placed output** (hello's included): `AbOffA`
of the runtime layout's labels is off every abort site of its marks. -/
theorem hoff_ofPlaceW : ∀ s c, Spike.Lib.X64WakeOff.AbOffA (RuntimeLayout.ofPlaceWX hp i).lab s c →
    ∀ k a, (Spike.Lib.X64.PhRec.μ (RuntimeLayout.ofPlaceWX hp i)).abortAt k = some a → pcOf s ≠ a :=
  fun _ _ h => Spike.Lib.X64AbOffL.off_of_A_ofPlaceOK hp i h

end Place

end Spike.Lib.X64HelloMainInv

/-- info: 'Spike.Lib.X64HelloMainInv.mainInvP_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloMainInv.mainInvP_closed

/-- info: 'Spike.Lib.X64HelloMainInv.hoff_ofPlaceW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloMainInv.hoff_ofPlaceW
