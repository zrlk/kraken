/-
**hello.w's root-instance premises, collected** (x86-64; twin of `Spike/Lib/A64HelloRootPrem.lean`). The `wc_main`
twins (`X64HelloWcWfS`, `X64HelloWcW1`, …) are generic in the root's choices; `HelloRootPrem L lbl` is the one
place where hello's root discharges them, for the runtime layout `L` and the start's labels `lbl`:

- the layout's facts: helloCells (`hp`), the code base (`hlo`), the abort label (`hΛ`), the labels (`hlab`), the
  take site (`hsite`), `.rodata` off the stack pool (`hro`);
- `hmid`'s premises at the box's level (`h2`: after rodata's allocation `l` and the box's `l'`): the arena `ar`,
  the box's landing side and frame condition (`msB`, `F0`), the level `W2`, its fence's extra `X2`, its memory side
  `ms2`, the box's extra ghost facts `G`, the level's extra fact at the clone `Wc`, and the named premises `hK2`,
  `hpub2`, `x2_off`, `hXr`, `hokb`, `hg`, `hP`; the clone's refusal is fixed, `ClH`;
- the callee's (`X64HelloTi2HatO.hti_HOX`'s) layout and level facts: the start's level parameters `Dt`, `Ctx`,
  `lsize`, `frM` (generic), the words' separation `hs`, the second stack in the pool `hsub`, the second TCB's
  words and the counters off the arena (`hmF`, `hnoF`, `hoffT`, `hoffL`, `hoffX`).

- `HelloRootPremG WS`: the premises with `hP` at the start level `WS` (`X64.HelloH1A.H1GAHG`); `HelloRootPrem` is
  it at `StartWf.WSH` (main's owned words `ownGH`), `HelloRootPremX` at `WSHX` (`ownGHXW`).
- `HelloRootPremG.hmidG`: `X64HelloHatA.hmid_boxAH` at the root's premises, given each ghost's `HMidPAH`;
  `HelloRootPremX.hmid` by `X64.HelloH1A.hMidPAH_ofX` (given the worker's TCB word off the counters; the root is at
  `ownGHXW`).

`ClH`, `Fresh2H`, `lbl2H` live in `Spike/Lib/X64HelloClH.lean` (same namespace).

## Unlike AArch64

- The code is `helloCells` with labels by `codeLabel` (AArch64 `helloProg`, `codeOf`); the kernel at `h2` is
  `X64.abi` (`hK2`); the source is `X64HelloSrc.helloSrc`.
- `hP`'s `H1GAHG` is x86-64's (`X64.HelloH1A.H1GAHG`: the box published at `.x25`'s `mfence`, the callees at `-136`),
  and the callee's take is `hti_HOX` inside `W ∧ X ∧ NoSetFsAt` (AArch64 `NoMsrAt`).
- AArch64 imports `A64HelloWcPl`, which nothing here reads; it has no twin.
- main also owns its own and the worker's TCB words up to the clone, so the premises are generic in the start
  level (`HelloRootPremG`), at `WSHX` for the root (AArch64: `HelloRootPrem` at `WSH` only).
-/
import Spike.Lib.X64HelloWcW1
import Spike.Lib.X64HelloHMid
import Spike.Lib.X64HelloWcInv3
import Spike.Lib.X64HelloClH
import Spike.Lib.X64HelloH1A

namespace Spike.Lib.X64.HelloPh

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (codeLabel)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl)
open Spike.Lib.X64.Alloc (Call)
open Spike.Lib.X64HelloHMid (BoxPureH BoxMH CloneMidH slWsH)
open Spike.Lib.X64HelloPreA (clonePcH)
open Spike.Lib.X64.Rt.PreChild (r1Of)
open Spike.Lib.X64.Flow.HelloWc (tH)

/-- **hello's root-instance premises at the start level `WS`** for the runtime layout `L` and the start's labels
`lbl`. -/
structure HelloRootPremG
    (WS : RuntimeLayout → BitVec 64 → Spike.Lib.Arena → Prog → (State → Prop) → (State → Prop) →
      Spike.Lib.FragS isa → Lbl → Spike.Lib.X64Consumer.Lsize → TermRun.Frame → (State → Prop) → Spike.Lib.Frag isa)
    (L : RuntimeLayout) (lbl : Lbl) : Type where
  hp : L.prog = SccCode.helloCells
  hlo : L.Λ.code.lo = lo
  hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName
  hlab : ∀ l x, codeLabel lo SccCode.helloCells l = some x → L.lab l = Int64.ofNat x
  hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat
  /-- `.rodata` off the stack pool (`hti_HOX`'s `hro`). -/
  hro : L.Λ.rodata.Disjoint L.Λ.stackPool
  /-- The allocator's arena. -/
  ar : Spike.Lib.Arena
  /-- The arena's geometry: the counter off its cells, the box sizes. -/
  har : ar.OK
  /-- The memory side the box's landing is stated at, per rodata's allocation (hello's box lands in `h1`'s
  segment, so the instance is `h1`'s side at no frames). -/
  msB : WeakMem.AllocLabel → Nat → Nat → Spike.Lib.MemSide isa
  /-- The box's frame condition. -/
  F0 : MachineData → Prop
  /-- The level after the box (hello's third level). -/
  W2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → Spike.Lib.FragS isa
  /-- The fence's extra fact at `h2`. -/
  X2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → Spike.Lib.FragS isa
  /-- `h2`'s memory side. -/
  ms2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame →
    Spike.Lib.MemSide isa
  /-- The box's ghost facts beyond `BoxPureH` (`hmid_boxAH`'s `G`). -/
  G : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat →
    Spike.Lib.Region → (MachineData → Prop) → (Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop) → UInt64 → Prop
  /-- The level's extra fact at the clone's `syscall`. -/
  Wc : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → Spike.Lib.Frag isa
  /-- `h2`'s kernel at no frames. -/
  hK2 : ∀ l b n l' b' n', Fresh2H ar lbl l b n l' b' n' → (ms2 l b n l' b' n' []).K = some Scc.Sem.X64.abi
  /-- `h2`'s publication at no frames. -/
  hpub2 : ∀ l b n l' b' n', Fresh2H ar lbl l b n l' b' n' → (ms2 l b n l' b' n' []).pub
  /-- `X2` off the clone's and the take site's pcs. -/
  x2_off : ∀ l b n l' b' n', Fresh2H ar lbl l b n l' b' n' → ∀ s c, Scc.Sem.X64.pcOf s ≠ clonePcH L →
    Scc.Sem.X64.pcOf s ≠ (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat →
    X2 l b n l' b' n' s c []
  /-- The box call's premises carry from `msB` to `h2`'s side. -/
  hokb : ∀ l b n l' b' n', Fresh2H ar lbl l b n l' b' n' →
    ∀ q : Call, q.OKB (msB l b n) L.lab → q.OKB (ms2 l b n l' b' n' []) L.lab
  /-- `h2`'s arena geometry `msB`'s. -/
  hg : ∀ l b n l' b' n', Fresh2H ar lbl l b n l' b' n' →
    (ms2 l b n l' b' n' []).heap = (msB l b n).heap ∧ (ms2 l b n l' b' n' []).cells = (msB l b n).cells ∧
      (ms2 l b n l' b' n' []).off = (msB l b n).off ∧ (ms2 l b n l' b' n' []).units = (msB l b n).units
  /-- The start's level's debts (`StartWf.WSH`'s `Dt`). -/
  Dt : State → Prop
  /-- The start's level's contexts (`WSH`'s `Ctx`). -/
  Ctx : Spike.Lib.FragS isa
  /-- The start's level's sizes (`WSH`'s `lsize`). -/
  lsize : Spike.Lib.X64Consumer.Lsize
  /-- main's frame per `wc_main` control (`WSH`'s `frM`; generic here). -/
  frM : Spike.Lib.Ctl → TermRun.Frame
  /-- The runtime's words separated at the reserve's counter. -/
  hs : Spike.Lib.X64.WakePh.WSep L (Spike.Lib.X64.Rt.Reserve.ntA L.lab)
  /-- The second stack in the pool. -/
  hsub : (r1Of L.lab).Sub L.Λ.stackPool
  /-- The second TCB's words mapped (`hti_HOX`'s `hmF`). -/
  hmF : ∀ a ∈ Spike.Lib.X64.Rt.Ti.tiAddrs (tH L.lab),
    Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 L.Λ) true ⟨a, 8⟩ = true
  /-- The second TCB's words off the owned words (`hti_HOX`'s `hnoF`). -/
  hnoF : ∀ b ∈ Spike.Lib.X64.Rt.Ti.tiAddrs (tH L.lab), ∀ j w,
    (⟨b, 8⟩, w) ∉ own2bH L (Spike.Lib.X64.Rt.Reserve.ntA L.lab) j
  /-- The second TCB's words off the arena. -/
  hoffT : ∀ b ∈ Spike.Lib.X64.Rt.Ti.tiAddrs (tH L.lab),
    ¬ (ar.heap ≤ b.toNat ∧ b.toNat < ar.heap + 16 * ar.cells) ∧ (⟨b, 8⟩ : Loc) ≠ ar.ctrLoc
  /-- The stack lock off the arena. -/
  hoffL : ¬ (ar.heap ≤ L.lockA.toNat ∧ L.lockA.toNat < ar.heap + 16 * ar.cells) ∧
    (⟨L.lockA, 8⟩ : Loc) ≠ ar.ctrLoc
  /-- The stack cursor off the arena. -/
  hoffX : ¬ (ar.heap ≤ L.nextA.toNat ∧ L.nextA.toNat < ar.heap + 16 * ar.cells) ∧
    (⟨L.nextA, 8⟩ : Loc) ≠ ar.ctrLoc
  /-- The site's range `r1Of` at the take site inside `W2 ∧ X2`. -/
  hXr : ∀ l b n l' b' n', Fresh2H ar lbl l b n l' b' n' → ∀ s c, W2 l b n l' b' n' s c [] →
    X2 l b n l' b' n' s c [] → s.st.2 = L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL →
    Scc.Sem.Kernel.siteRange Scc.Sem.X64.abi s = r1Of L.lab
  /-- `h1`'s open premises at every ghost of the box: `X64.HelloH1A.H1GAHG` at `h2`'s level, side and placement,
  the start level `WS` at `ntA`, `ar`, `Dt`, `ClH`, `Ctx`, `lsize`, `frM`; at `WS := WSHX` (`H1GAHX`)
  `hMidPAH_ofX` makes `X64HelloHatA.HMidPAH` of it (the callee `ti` by `hti_HOX`, inside `W ∧ X ∧ NoSetFsAt` under
  `TakeCK site r1Of ClH`).

  Satisfiable: the antecedent `BoxPureH ∧ G` is exactly the ghost part of `BoxMH` at the box's landing (`hmid`'s
  pre), so `hP` is consumed only at the ghosts of the real run's landing; with `G := H1GAHG …` itself,
  `hP := fun _ _ _ _ _ _ _ _ _ _ _ h => h`. -/
  hP : ∀ l b n l' b' n', Fresh2H ar lbl l b n l' b' n' → ∀ R F J1 t, BoxPureH L F0 n' R F J1 t →
    G l b n l' b' n' R F J1 t →
    Spike.Lib.X64.HelloH1A.H1GAHG L (W2 l b n l' b' n') (X2 l b n l' b' n') (Wc l b n l' b' n')
      (ms2 l b n l' b' n') Spike.Lib.X64HelloSrc.helloSrc (lbl2H lbl l b l' b') l' b' (slWsH l) ar
      (fun c0 => WS L (Spike.Lib.X64.Rt.Reserve.ntA L.lab) ar Spike.Lib.X64HelloSrc.helloSrc Dt (ClH L) Ctx
        (lbl2H lbl l b l' b') lsize (frM c0)
        (Spike.Lib.X64.HelloPh.Ti2.X0TH L (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL)))
      R F J1 t

/-- **hello's root-instance premises** at the start level `StartWf.WSH` (main's owned words `ownGH`). -/
abbrev HelloRootPrem (L : RuntimeLayout) (lbl : Lbl) : Type :=
  HelloRootPremG Spike.Lib.X64.HelloPh.StartWf.WSH L lbl

/-- **hello's root-instance premises at the self words**: at the start level `WSHX` (main's owned words
`ownGHXW`). -/
abbrev HelloRootPremX (L : RuntimeLayout) (lbl : Lbl) : Type :=
  HelloRootPremG WSHX L lbl

namespace HelloRootPremG

variable {WS : RuntimeLayout → BitVec 64 → Spike.Lib.Arena → Prog → (State → Prop) → (State → Prop) →
  Spike.Lib.FragS isa → Lbl → Spike.Lib.X64Consumer.Lsize → TermRun.Frame → (State → Prop) → Spike.Lib.Frag isa}
  {L : RuntimeLayout} {lbl : Lbl} (P : HelloRootPremG WS L lbl)

/-- **`hmid` at `h2`'s indices at any start level** (`X64HelloHatA.hmid_boxAH` at the root's premises), given
each ghost's `HMidPAH` from `hP`'s `H1GAHG` (`hM`). -/
theorem hmidG {l : WeakMem.AllocLabel} {b n : Nat} {l' : WeakMem.AllocLabel} {b' n' : Nat}
    (hf : Fresh2H P.ar lbl l b n l' b' n')
    (hM : ∀ R F J1 t, BoxPureH L P.F0 n' R F J1 t →
      Spike.Lib.X64.HelloH1A.H1GAHG L (P.W2 l b n l' b' n') (P.X2 l b n l' b' n') (P.Wc l b n l' b' n')
        (P.ms2 l b n l' b' n') Spike.Lib.X64HelloSrc.helloSrc (lbl2H lbl l b l' b') l' b' (slWsH l) P.ar
        (fun c0 => WS L (Spike.Lib.X64.Rt.Reserve.ntA L.lab) P.ar Spike.Lib.X64HelloSrc.helloSrc P.Dt (ClH L) P.Ctx
          (lbl2H lbl l b l' b') P.lsize (P.frM c0)
          (Spike.Lib.X64.HelloPh.Ti2.X0TH L (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL)))
        R F J1 t →
      Spike.Lib.X64HelloHatA.HMidPAH L (P.W2 l b n l' b' n') (P.X2 l b n l' b' n') (P.Wc l b n l' b' n')
        (P.ms2 l b n l' b' n') Spike.Lib.X64HelloSrc.helloSrc (lbl2H lbl l b l' b') (ClH L) l' b' (slWsH l)
        R F J1 t) :
    Spike.Lib.SegWS (fun s c fs => P.W2 l b n l' b' n' s c fs ∧ P.X2 l b n l' b' n' s c fs)
      (Spike.Lib.X64ConsumerA.TakeCKS (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL) (ClH L))
      Spike.Lib.X64HelloSrc.helloSrc (lbl2H lbl l b l' b') (P.ms2 l b n l' b' n')
      (fun s c fs => BoxMH L (P.msB l b n) P.F0 (P.G l b n l' b' n') l' b' (slWsH l) n' s c ∧
        Spike.Lib.X64.KeepUn.U (r1Of L.lab) s ∧ fs = [])
      (CloneMidH L P.F0 (P.G l b n l' b' n') (P.W2 l b n l' b' n') (P.Wc l b n l' b' n') l' b' (slWsH l) n') :=
  Spike.Lib.X64HelloHatA.hmid_boxAH P.hp (P.hK2 _ _ _ _ _ _ hf) (P.hpub2 _ _ _ _ _ _ hf) (fun _ h => ClH.pc h)
    (P.x2_off _ _ _ _ _ _ hf) (P.hXr _ _ _ _ _ _ hf) (Spike.Lib.X64.Rt.fitS_of_sub L P.hsub)
    (P.hokb _ _ _ _ _ _ hf) (P.hg _ _ _ _ _ _ hf)
    fun R F J1 t hB hG => hM R F J1 t hB (P.hP _ _ _ _ _ _ hf _ _ _ _ hB hG)

end HelloRootPremG

namespace HelloRootPremX

variable {L : RuntimeLayout} {lbl : Lbl} (P : HelloRootPremX L lbl)

/-- **`hmid` at `h2`'s indices at the self words** (`HelloRootPremG.hmidG`, `HMidPAH` by
`X64.HelloH1A.hMidPAH_ofX`), given the worker's TCB word off the counters and `ntA` (`hW`). -/
theorem hmid (hW : Spike.Lib.X64HelloOwnLift.tcbWH L ∉
      [L.pnA, L.lockA, L.freeNA, L.nextA, Spike.Lib.X64.Rt.Reserve.ntA L.lab])
    {l : WeakMem.AllocLabel} {b n : Nat} {l' : WeakMem.AllocLabel} {b' n' : Nat}
    (hf : Fresh2H P.ar lbl l b n l' b' n') :
    Spike.Lib.SegWS (fun s c fs => P.W2 l b n l' b' n' s c fs ∧ P.X2 l b n l' b' n' s c fs)
      (Spike.Lib.X64ConsumerA.TakeCKS (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL) (ClH L))
      Spike.Lib.X64HelloSrc.helloSrc (lbl2H lbl l b l' b') (P.ms2 l b n l' b' n')
      (fun s c fs => BoxMH L (P.msB l b n) P.F0 (P.G l b n l' b' n') l' b' (slWsH l) n' s c ∧
        Spike.Lib.X64.KeepUn.U (r1Of L.lab) s ∧ fs = [])
      (CloneMidH L P.F0 (P.G l b n l' b' n') (P.W2 l b n l' b' n') (P.Wc l b n l' b' n') l' b' (slWsH l) n') :=
  HelloRootPremG.hmidG P hf fun _ _ _ _ hB hG => Spike.Lib.X64.HelloH1A.hMidPAH_ofX P.hp P.hlo P.hlab P.hsite
    P.hΛ (fun _ h => h.2) (fun _ h => ClH.pc h) P.hs P.hro hW P.hsub P.hmF P.hnoF P.hoffT P.hoffL P.hoffX hB hG

end HelloRootPremX

end Spike.Lib.X64.HelloPh

/-- info: 'Spike.Lib.X64.HelloPh.HelloRootPremG.hmidG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.HelloRootPremG.hmidG

/-- info: 'Spike.Lib.X64.HelloPh.HelloRootPremX.hmid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.HelloRootPremX.hmid
