/-
**hello.w's box past its store to main's `clone`: the ghosts, the source facts and the clone's state** (x86-64;
the twin of `Spike/Lib/A64HelloHMid.lean`, at hello's `wc_main`, frame 128). The pieces the hat from the box's
landing `bXH` to main's clone uses: the landing's ghosts (`BoxPureH`), the box's source facts (`QBH`) and the
source at the clone (`SBH`, the box's slice words kept), the fence off the clone's and the take site's pcs
(`WBH`), and main at the clone's `syscall` (`CloneMidH`), which is `ClonePostH`.

- `at_bXH_ms`: the landing across memory sides admitting the same box calls (wake's `at_bX_ms`).
- `BoxPureH`: the box's facts of its ghosts alone (`R`, `F`, `J1`, `t`, `n`) that the hat and `ClonePostH` use
  (wake's `BoxPure`); the instance's other ghost facts are the extra `G`.
- `slWsH`: rodata's slice words (the instance's `ws`).
- `QBH`, `SBH`: the box's source facts and the source at the clone (wake's `QB`, `SB`).
- `BoxMH`: the box's landing with its ghosts (the pre; wake's `Box`'s shape).
- `WBH`: the level at no frames off the clone's and the take site's pcs (wake's `WB`).
- `CloneMidH`: main at the clone's `syscall` (wake's `CloneP`); `CloneMidH.post`: it is `ClonePostH`.
- `pin8_toBitVec`: `t = pinA + 8` as numbers is so as words.

No absolute address appears in this file.

## Differences from the AArch64 version

- `BoxPureH` asks `R.lo ≤ -384` and `16 ≤ R.hi` (the bounds of `X64HelloWcHatK.hello_wc_mid_hatK`; AArch64
  `-400`, `0`) and puts the base 96 below stack 0's top (`wc_main`'s base is `%rsp + 128`, `%rsp` 224 below the
  top; AArch64: 80, from `sp + 144`).
- `CloneMidH` reads the base as `%rsp + 128` (AArch64 `SP + 144`); the thread pointer is `fsBase` (`TP`).
- The x86-64 landing `bXH` carries the allocator's counter fact (`∃ o, …`) as its own component; `at_bXH_ms`
  rewrites it along the arena geometry `hg`.
- Only the live constants are twinned: the named premises `HMidPH` and the composite `hmid_boxH` are not.
-/
import Spike.Lib.X64HelloWcHatK
import Spike.Lib.X64HelloWcW1
import Spike.Lib.X64HelloWcInv
import Spike.Lib.X64HelloMainPreSrc

namespace Spike.Lib.X64HelloHMid

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.HelloWc (bXH FrMGH tH clonePostH_of)
open Spike.Lib.X64.HelloPh.WcSp6 (wcNSH)
open Spike.Lib.X64.Flow.WakeWc (kOf)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.KeepTP (TP)
open Spike.Lib.X64HelloPreA (ClonePostH clonePcH)
open Spike.Lib.X64HelloMainPreSrc (SpawnSrcH boxTermH)
open Spike.Lib.X64HelloSplit (slTy)
open Spike.Lib.X64WakeSrcDefs (mainTidLbl)
open Scc.Sem.X64 (pcOf)

/-- **The landing across memory sides** admitting the same box calls, with the same arena geometry (`heap`,
`cells`, `off`, `units`). -/
theorem at_bXH_ms {ms ms' : MemSide isa} {exe : _root_.Executable} {endPc : Int64} {R : Region}
    {F : MachineData → Prop} {J1 : AS → Ctl → Prop} {l : WeakMem.AllocLabel} {A : Nat} {s : State} {c : Ctl}
    (hq : ∀ q : Spike.Lib.X64.Alloc.Call, q.OKB ms (_root_.Executable.labels exe).label →
      q.OKB ms' (_root_.Executable.labels exe).label)
    (hg : ms'.heap = ms.heap ∧ ms'.cells = ms.cells ∧ ms'.off = ms.off ∧ ms'.units = ms.units)
    (h : At exe endPc R F (bXH ms (_root_.Executable.labels exe).label J1 l A) s c) :
    At exe endPc R F (bXH ms' (_root_.Executable.labels exe).label J1 l A) s c := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, q, h1, h2, h3, h4⟩ := h
  obtain ⟨g1, g2, g3, g4⟩ := hg
  exact ⟨he, hn, hdc, hpc, σ, hA, hD, ⟨q.1, hq _ q.2⟩, h1, h2, h3, by rw [g1, g2, g3, g4]; exact h4⟩

/-- **The box's facts of its ghosts alone** that the hat and `ClonePostH` use: the region `R` (room for
`wc_main`'s callees, `R.lo ≤ -384`, `16 ≤ R.hi`; its base 96 below stack 0's top), the frame condition `F`
(inside `F0`), the thread pointer `t = pinA + 8`, one object. -/
def BoxPureH (L : RuntimeLayout) (F0 : MachineData → Prop) (n : Nat) (R : Region) (F : MachineData → Prop)
    (_J1 : AS → Ctl → Prop) (t : UInt64) : Prop :=
  R.OK ∧ R.base.toNat % 16 = 0 ∧ FStable R F ∧ R.lo ≤ -384 ∧ 16 ≤ R.hi ∧
    R.base.toNat + 96 = L.stacksA.toNat + 16384 ∧ t.toNat = L.pinA.toNat + 8 ∧ n = 1 ∧ ∀ m, F m → F0 m

/-- **rodata's slice words** at its label `l` (`SlRep`'s shape): the buffer `l`, `m = 2`, `n = 13`; the
instance's `ws`. -/
def slWsH (l : WeakMem.AllocLabel) : List TermRun.Word :=
  [TermRun.cst (.loc ⟨l, 0⟩ 0), TermRun.cst (.num 2), TermRun.cst (.num 13)]

/-- **The box's source facts** at `l` (`b`): `boxTermH`, no hold, `o` at `l`'s owned locative, `me` at main's,
`sl` at the words `ws`. -/
def QBH (l : WeakMem.AllocLabel) (b : Nat) (ws : List TermRun.Word) (l' : WeakMem.AllocLabel) (A : Nat) (c : Ctl) :
    Prop :=
  l' = l ∧ A = b ∧ c.term = boxTermH ∧ c.hold = none ∧
    TermRun.evalAt c.env (.var "o") = some (.ptr .own .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) ∧
    TermRun.evalAt c.env (.var "me") = some (.tid, [TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)]) ∧
    TermRun.evalAt c.env (.var "sl") = some (slTy, ws)

/-- **The source at the clone** at `l` (`b`): `SpawnSrcH l ws` at the box's words `ws`. -/
def SBH (l : WeakMem.AllocLabel) (b : Nat) (ws : List TermRun.Word) (l' : WeakMem.AllocLabel) (A : Nat) (c : Ctl) :
    Prop :=
  l' = l ∧ A = b ∧ SpawnSrcH l ws c

/-- **The box's landing with its ghosts** at `l`, `b`, `n` under `ms0`: `BoxPureH` and the instance's extra `G`
at the ghosts, `bXH` with the thread pointer `t`, the source facts `QBH`. -/
def BoxMH (L : RuntimeLayout) (ms0 : MemSide isa) (F0 : MachineData → Prop)
    (G : Region → (MachineData → Prop) → (AS → Ctl → Prop) → UInt64 → Prop) (l : WeakMem.AllocLabel) (b : Nat)
    (ws : List TermRun.Word) (n : Nat) (s : State) (c : Ctl) : Prop :=
  ∃ (R : Region) (F : MachineData → Prop) (J1 : AS → Ctl → Prop) (t : UInt64),
    BoxPureH L F0 n R F J1 t ∧ G R F J1 t ∧
    (At L.exe L.endPc R F (bXH ms0 L.lab J1 l b) s c ∧ TP t s) ∧ QBH l b ws l b c

/-- **The fence the hat runs in**: the level `W` at no frames, off the clone's pc and the take site's. -/
def WBH (L : RuntimeLayout) (W : FragS isa) : Frag isa := fun s c =>
  W s c [] ∧ pcOf s ≠ clonePcH L ∧ pcOf s ≠ (L.lab Ret0.StackTake.siteL).toBitVec.toNat

/-- **main at the clone's `syscall`** (the hat's post with the box's ghosts; wake's `CloneP`): no frames, inside
`W` and `Wc`, at `wcNSH` in the box's region (base `%rsp + 128`) with `BoxPureH` and `G` at its ghosts, the
caller's saves `FrMGH`, the box's cell `b`, the source at `SpawnSrcH l ws` (the box's words `ws`), the thread
pointer `t`. -/
def CloneMidH (L : RuntimeLayout) (F0 : MachineData → Prop)
    (G : Region → (MachineData → Prop) → (AS → Ctl → Prop) → UInt64 → Prop) (W : FragS isa)
    (Wc : Frag isa) (l : WeakMem.AllocLabel) (b : Nat) (ws : List TermRun.Word) (n : Nat) : FragS isa :=
  fun s c fs =>
  fs = [] ∧ W s c [] ∧ Wc s c ∧
    ∃ (R : Region) (F : MachineData → Prop) (J1 : AS → Ctl → Prop) (t : UInt64)
      (sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) (me cA : BitVec 64) (fr : BitVec 64 × BitVec 64),
      BoxPureH L F0 n R F J1 t ∧ G R F J1 t ∧ FrMGH J1 fr sl me ∧ cA.toNat = b ∧ SpawnSrcH l ws c ∧
      At L.exe L.endPc R F (wcNSH L.lab c (tH L.lab) (kOf L.lab) sl me cA fr) s c ∧
      (R.base.toNat : Int) = (s.st.1.regs.get64 .rsp).toNat + 128 ∧ TP t s

/-- `t = pinA + 8` as numbers is so as words. -/
theorem pin8_toBitVec {L : RuntimeLayout} {t : UInt64} (ht : t.toNat = L.pinA.toNat + 8) :
    t.toBitVec = L.pinA + 0#64 + 8#64 := by
  apply BitVec.eq_of_toNat_eq
  have h1 := t.toBitVec.isLt; have h2 := L.pinA.isLt; have ht' : t.toBitVec.toNat = _ := ht
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- **main at the clone's `syscall` is `ClonePostH`** (`clonePostH_of`; `%rsp + 224` is stack 0's top since the
base is both `%rsp + 128` and 96 below the top). -/
theorem CloneMidH.post {L : RuntimeLayout} {F0 : MachineData → Prop}
    {G : Region → (MachineData → Prop) → (AS → Ctl → Prop) → UInt64 → Prop} {W : FragS isa}
    {Wc : Frag isa} {l : WeakMem.AllocLabel} {b n : Nat} {ws : List TermRun.Word} {s : State} {c : Ctl}
    {fs : List TermRun.Frame} (h : CloneMidH L F0 G W Wc l b ws n s c fs) : ∃ t, ClonePostH L L.endPc t s c := by
  obtain ⟨-, -, -, R, F, J1, t, sl, me, cA, fr, ⟨-, hal, -, -, -, htop, ht, -⟩, -, -, -, -, hA, hb, htp⟩ := h
  exact ⟨t, clonePostH_of hal hA hb htp (by omega) (pin8_toBitVec ht)⟩

end Spike.Lib.X64HelloHMid

/-- info: 'Spike.Lib.X64HelloHMid.at_bXH_ms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloHMid.at_bXH_ms

/-- info: 'Spike.Lib.X64HelloHMid.pin8_toBitVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloHMid.pin8_toBitVec

/-- info: 'Spike.Lib.X64HelloHMid.CloneMidH.post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloHMid.CloneMidH.post
