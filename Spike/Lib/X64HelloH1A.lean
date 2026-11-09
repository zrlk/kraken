/-
**`HMidPAH` from `h1`'s open premises at one ghost of the box** (x86-64; twin of `Spike/Lib/A64HelloH1A.lean`, the
hello counterpart of wake's `H1GA`/`hMidPA_of`): every field of `X64HelloHatA.HMidPAH` from the ghost's open facts
`H1GAHX`, the callee's `ti` by `X64HelloTi2HatO.hti_HOX`.

`hti_HOX`'s premises split three ways. The layout's (`hp`, `hlo`, `hlab`, `hsite`, `hΛ`, `hs`, `hro`, `hsub`), the
second TCB's words and the counters off the arena (`hmF`, `hnoF`, `hoffT`, `hoffL`, `hoffX`) and the refusals'
(`hcl`, `hCl`) are `hMidPAH_ofX`'s, with the worker's TCB word off the counters (`hW`); `BoxPureH` gives the box's
base and bounds (`hbase`, `hRs`); the box's source facts give `hSctl` (`HelloH1A.sctl_midQBH`); the rest, per
ghost, is `H1GAHX`'s.

- `H1GAHG`: `h1`'s open premises at one ghost (wake's `H1GA`), the start's level `V` a parameter; `H1GAHX` is it
  at `WSHX` (the start's level at `ownGHXW`; AArch64's `H1GAH` is at `WSH`).
- `hMidPAH_ofX`: `HMidPAH` from `BoxPureH` and `H1GAHX` (wake's `hMidPA_of`), the callee's `ti` by
  `X64HelloTi2HatO.hti_HOX`, given the worker's TCB word off the counters and `a` (`hW`).

The source lemmas at the clone (`frameRun_spawnH`, `spawnSrcH_ctl`, `sctl_SBH`, `sctl_QBH`, `sctl_midQBH`) are
`X64HelloH1ASrc`'s, in the same namespace. `WSHX`'s arena `ar`, debts `Dt`, refusal `Cw`, contexts `Ctx`, sizes
`lsize` and main frame `frM` stay free (the root picks them). No absolute address appears in this file.

## Unlike AArch64

- The box is published at `.x25`'s `mfence`, so `wcWf`, `tcb`, `hWX` and `hpl` are at `MidG (QBH l b ws)` and
  `hSctl` is `sctl_midQBH` (AArch64: `SBH`, `sctl_SBH`).
- The callees sit at `-136` (`rARH R = R.callee (-136) (-40) 8`, the TCB's `R.callee (-136) (-184) 8`, the take's
  `R' = R.callee (-136) (-248) 8` and `R'.callee (-48) (-200) 8`; AArch64 `-144`, `-48`, `-192`, `-256`, `-208`,
  `hi' = 0`); the reserve returns to `.Lwc_main.x1`, the TCB's allocation to `x24L` (AArch64 `.sp3`, `.sp4`).
- `R`'s end below the second stack is `hi96 : R.hi ≤ 96` (AArch64 `hi80`), and `BoxPureH`'s `16 ≤ R.hi` gives the
  callee's `8 ≤ R.hi`; the header and thread init's stores are `Ret0.StOk (ms []) F` (no `exe`, `endPc`).
- The thread pointer is `fsBase`: `ms.K = some X64.abi` (`hK`), `KeepUn.U` is x86-64's.
-/
import Spike.Lib.X64HelloH1ASrc
import Spike.Lib.X64HelloHatA
import Spike.Lib.X64HelloTi2HatO
import Spike.Lib.X64HelloW2Weak

namespace Spike.Lib.X64.HelloH1A

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.HelloWc (WcMainWH FrMGH rNH ResCtxH TcbCtxH wcNCRH tcb2QH tH rARH x24L)
open Spike.Lib.X64.HelloPh.WcSp6 (wcNSH)
open Spike.Lib.X64.Flow.WakeWc (MidG kOf tiQ)
open Spike.Lib.X64.Flow.Ret0 (CallerCells StackM StOk)
open Spike.Lib.X64.Flow.Ret0.StackTake (siteL)
open Spike.Lib.X64.Rt (TcbOkGA hdrA RuntimeLayout TcbWG)
open Spike.Lib.X64.Rt.Reserve (ResOkA ReserveW)
open Spike.Lib.X64.Rt.PreChild (r1Of)
open Spike.Lib.X64.KeepTP (tpXa)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64HelloHMid (BoxPureH QBH)
open Spike.Lib.X64HelloHatA (HMidPAH)
open Spike.Lib.X64HelloPreA (clonePcH)
open Spike.Lib.X64HelloMainPreSrc (SpawnSrcH)
open Spike.Lib.X64.HelloPh.Ti2 (X0TH SlotPH SlotSlH)
open Spike.Lib.X64.HelloPh (lo WSHX)
open Scc.Sem.X64 (pcOf abi codeLabel)

/-! ## The open premises at one ghost -/

/-- **`h1`'s open premises at one ghost of the box, at any start level** (`R`, `F`, `J1`, `tp`) with the callee's
take, inside the level `W`, its fence's extra `X`, the clone's extra `Wc`, under `ms`, for the source `p`, the
placement `lbl`, the box's label `l` at `b` with the slice's words `ws`, the arena `ar`; the start's level at main's
frame `V c0` (`H1GAHX`: `WSHX`): `HMidPAH`'s fields but `ti`, and the callee's per-ghost premises
(wake's `H1GA`). -/
structure H1GAHG (L : RuntimeLayout) (W X : FragS isa) (Wc : Frag isa)
    (ms : List TermRun.Frame → MemSide isa) (p : Prog) (lbl : Lbl) (l : WeakMem.AllocLabel) (b : Nat)
    (ws : List TermRun.Word) (ar : Arena) (V : Ctl → Frag isa) (R : Region) (F : MachineData → Prop)
    (J1 : AS → Ctl → Prop) (tp : UInt64) :
    Prop where
  /-- `HMidPAH.wcWf`. -/
  wcWf : WcMainWH (fun s c => W s c []) (fun _ _ => False) L.exe L.endPc R F F (tpXa (ms []) tp) J1 (QBH l b ws)
  /-- `HMidPAH.res`. -/
  res : ∀ g : Ret0.AllocTcb.G × Ctl, g.1.ra = (L.lab ".Lwc_main.x1").toBitVec →
    ∀ nd, ReserveW (fun s c => W s c []) (fun _ _ => False) L.exe L.endPc (rARH R)
      (fun m => F m ∧ CallerCells R (-136) (-40) 8 m ∧ ResCtxH L.lab R
        (rNH (tpXa (ms []) tp) L.lab R J1 (QBH l b ws) .call).J g m) ⟨g.1, 0#64, g.2⟩ nd
  /-- `HMidPAH.tcb`. -/
  tcb : ∀ c0 sl me cA fr, MidG (QBH l b ws) c0 cA ∧ FrMGH J1 fr sl me →
    ∀ g : Ret0.AllocTcb.G, g.ra = (L.lab x24L).toBitVec →
    ∀ nd, TcbWG (fun s c => W s c []) (fun _ _ => False) L.exe L.endPc (R.callee (-136) (-184) 8)
      (fun mm => F mm ∧ CallerCells R (-136) (-184) 8 mm ∧
        TcbCtxH L.lab R (wcNCRH L.lab c0 sl me cA fr).J c0 g mm)
      (tcb2QH g c0) nd
  /-- `HMidPAH.resA`. -/
  resA : ∀ g : Ret0.AllocTcb.G × Ctl, ResOkA (ms []) F L.exe L.endPc (rARH R) F ⟨g.1, 0#64, g.2⟩
  /-- `HMidPAH.hdrA`. -/
  hdrA : ∀ c0 g, StOk (ms []) F (hdrA L.lab (tcb2QH g c0)) ((tcb2QH g c0).h ||| 1#64 <<< 36)
  /-- `HMidPAH.tcbA`. -/
  tcbA : ∀ c0 g, TcbOkGA (ms []) F L.exe L.endPc (R.callee (-136) (-184) 8) F (tcb2QH g c0)
  /-- `HMidPAH.tid`. -/
  tid : (ms []).rt (tH L.lab + 56#64).toNat ∧ (ms []).mp ⟨tH L.lab + 56#64, 8⟩ true ∧
    (ms []).G ⟨tH L.lab + 56#64, 8⟩ ((1#64).setWidth 128) ∧
    ∀ m', F m' → Mem.loadInt m'.dmem (tH L.lab + 56#64) 8 = none
  /-- `HMidPAH.wcl`. -/
  wcl : ∀ s c sl me cA fr, At L.exe L.endPc R F (wcNSH L.lab c (tH L.lab) (kOf L.lab) sl me cA fr) s c →
    SpawnSrcH l ws c → cA.toNat = b → FrMGH J1 fr sl me → StackM (r1Of L.lab) s.st.1 → W s c [] ∧ Wc s c
  /-- `HMidPAH.hi96`. -/
  hi96 : R.hi ≤ 96
  /-- `HMidPAH.fcl`. -/
  fcl : ∀ m pm, F m → F (Ret0.takeMem pm (r1Of L.lab) m)
  /-- `HMidPAH.fcg`. -/
  fcg : ∀ m m' : MachineData, m'.dmem = m.dmem → F m → F m'
  /-- `R`'s bounds 8-aligned (`hti_HOX`'s `hR8`). -/
  hR8 : R.lo % 8 = 0 ∧ R.hi % 8 = 0
  /-- The level lift from the start's level `V` at main's frame, at a state writing off the arena (`hti_HOX`'s /
  `hti_HOX`'s `hWX`). -/
  hWX : ∀ c0 cA, MidG (QBH l b ws) c0 cA → ∀ s c, V c0 s c → Spike.Lib.X64.HelloW2.OffW ar s → W s c [] ∧ X s c []
  /-- `c0` placed at main's slots, the box's cell's, main's id's and the slice's (`hti_HOX`'s `hpl`). -/
  hpl : ∀ c0 sl me cA fr, MidG (QBH l b ws) c0 cA ∧ FrMGH J1 fr sl me → ∀ s : State,
    SlotPH R b me.toNat s.st.1 ∧ SlotSlH R sl.1.toNat sl.2.2.1.toNat sl.2.2.2.toNat s.st.1 →
    Spike.Lib.X64ConsumerS.PlacedSE L.Λ lbl s c0 []
  /-- `F` inside the runtime's frame (`hti_HOX`'s `hFr`). -/
  hFr : ∀ m, F m → Spike.Lib.X64.Rt.rtF L m
  /-- The second TCB's words unmapped under `F` (`hti_HOX`'s `hunF`). -/
  hunF : ∀ a ∈ Spike.Lib.X64.Rt.Ti.tiAddrs (tH L.lab), ∀ m, F m → Mem.loadInt m.dmem a 8 = none
  /-- Main's stack off `R` under `F` (`hti_HOX`'s `hF0`). -/
  hF0 : ∀ m, F m → Ret0.StackOff (Spike.Lib.X64.Rt.Ti2.r0Of L.lab) R m
  /-- The thread init's fields (`hti_HOX`'s `hfld`). -/
  hfld : ∀ e ∈ Ret0.ThreadInit.fields (tH L.lab) (Ret0.stacksA L.lab + 16384#64),
    StOk (ms []) F (tH L.lab + BitVec.ofNat 64 e.1) e.2
  /-- The take's facts (`hti_HOX`'s `htk`). -/
  htk : ∀ (c0 : Ctl) (R' : Region) (F' : MachineData → Prop), (∀ m, F' m → F m) →
    R' = R.callee (-136) (-248) 8 → ∀ (g g' : Ret0.AllocTcb.G),
    Spike.Lib.X64.Rt.TakeOkA (ms []) F L.exe L.endPc (R'.callee (-48 - 0) (-200) 8) F'
      (Ret0.tiTake (tiQ (tH L.lab) c0 g) g')

/-- **`H1GAHG` at `WSHX`** (the start's level at `ownGHXW`, main's and the worker's TCB words owned; `hti_HOX`'s
premises): `WSHX`'s parameters `a`, `ar`, `Dt`, `Cw`, `Ctx`, `lsize`, `frM`. -/
abbrev H1GAHX (L : RuntimeLayout) (W X : FragS isa) (Wc : Frag isa)
    (ms : List TermRun.Frame → MemSide isa) (p : Prog) (lbl : Lbl) (l : WeakMem.AllocLabel) (b : Nat)
    (ws : List TermRun.Word) (a : BitVec 64) (ar : Arena) (Dt Cw : State → Prop) (Ctx : FragS isa) (lsize : Lsize)
    (frM : Ctl → TermRun.Frame) (R : Region) (F : MachineData → Prop) (J1 : AS → Ctl → Prop) (tp : UInt64) : Prop :=
  H1GAHG L W X Wc ms p lbl l b ws ar
    (fun c0 => WSHX L a ar p Dt Cw Ctx lbl lsize (frM c0) (X0TH L (L.lab siteL))) R F J1 tp

/-- **`HMidPAH` from `H1GAHX`** (AArch64 `hMidPAH_of` at `WSHX`, the callee's `ti` by `hti_HOX`): the worker's TCB
word off the counters and `a` (`hW`). -/
theorem hMidPAH_ofX {L : RuntimeLayout} {W X : FragS isa} {Wc : Frag isa}
    {ms : List TermRun.Frame → MemSide isa} {p : Prog} {lbl : Lbl} {Cl : State → Prop}
    {l : WeakMem.AllocLabel} {b n : Nat} {ws : List TermRun.Word} {a : BitVec 64} {ar : Arena} {Dt Cw : State → Prop}
    {Ctx : FragS isa} {lsize : Lsize} {frM : Ctl → TermRun.Frame} {F0 : MachineData → Prop}
    {R : Region} {F : MachineData → Prop} {J1 : AS → Ctl → Prop} {tp : UInt64}
    (hp : L.prog = SccCode.helloCells) (hlo : L.Λ.code.lo = lo)
    (hlab : ∀ l x, codeLabel lo SccCode.helloCells l = some x → L.lab l = Int64.ofNat x)
    (hsite : (Spike.Lib.X64.PhRec.μ L).site .take = some (L.lab siteL).toBitVec.toNat)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hcl : ∀ s, Cw s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hCl : ∀ s, Cl s → pcOf s = clonePcH L)
    (hs : Spike.Lib.X64.WakePh.WSep L a) (hro : L.Λ.rodata.Disjoint L.Λ.stackPool)
    (hW : Spike.Lib.X64HelloOwnLift.tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
    (hsub : (r1Of L.lab).Sub L.Λ.stackPool)
    (hmF : ∀ a ∈ Spike.Lib.X64.Rt.Ti.tiAddrs (tH L.lab),
      Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 L.Λ) true ⟨a, 8⟩ = true)
    (hnoF : ∀ b ∈ Spike.Lib.X64.Rt.Ti.tiAddrs (tH L.lab), ∀ j w,
      (⟨b, 8⟩, w) ∉ Spike.Lib.X64.HelloPh.own2bH L a j)
    (hoffT : ∀ b ∈ Spike.Lib.X64.Rt.Ti.tiAddrs (tH L.lab),
      ¬ (ar.heap ≤ b.toNat ∧ b.toNat < ar.heap + 16 * ar.cells) ∧ (⟨b, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hoffL : ¬ (ar.heap ≤ L.lockA.toNat ∧ L.lockA.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨L.lockA, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hoffX : ¬ (ar.heap ≤ L.nextA.toNat ∧ L.nextA.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨L.nextA, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hB : BoxPureH L F0 n R F J1 tp) (hG : H1GAHX L W X Wc ms p lbl l b ws a ar Dt Cw Ctx lsize frM R F J1 tp) :
    HMidPAH L W X Wc ms p lbl Cl l b ws R F J1 tp := by
  obtain ⟨-, -, -, hRlo, hhi, hbase, -⟩ := hB
  exact ⟨hG.wcWf, hG.res, hG.tcb, hG.resA, hG.hdrA, hG.tcbA, hG.tid, hG.hi96, hG.fcl, hG.fcg,
    Spike.Lib.X64HelloTi2HatO.hti_HOX hp hlo hlab hsite hΛ hcl hCl hG.hWX hs hW hro sctl_midQBH hG.hpl hG.hFr hmF
      hG.hunF hnoF hoffT hoffL hoffX hbase ⟨hRlo, by omega⟩ hG.hR8 hsub hG.hF0 hG.hfld hG.htk, hG.wcl⟩

end Spike.Lib.X64.HelloH1A

/-! ## Axioms -/

/-- info: 'Spike.Lib.X64.HelloH1A.hMidPAH_ofX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloH1A.hMidPAH_ofX
