/-
**hello's root premises from their base** (AArch64; row: the RootPrem instance builder): the
choices `HelloRootPrem` leaves free that the h1/h2 chains fix, made once, and the named premises they discharge,
derived (`H1GAH0V`'s `res`/`tcb` are `CalRootI.res_I`/`tcb_I`, assembled in `RootInstW.h0V_I`; the thread
init's writes off the arena are the segment's, `Ti2OffW.ti2_WSH_off`, so the base carries no open premise).

- `W2I`, `X2I`, `WcI`, `GI`: the third level (no frames and `HelloW2.W2H`, the empty context, at `ntA`,
  `helloSrc`, `ClH`, the level-1 placement and sizes; B8-W2H), the fence fact `X2H` at the take site
  and the level's sizes (`h2Stmt_root`'s `hX2`, at `ls0 := ls0T ls`), the clone fact `StackM r1Of`
  (`h2Stmt_root`'s `hWc` by `id`), the ghosts `RootHP.GJ1RH`
  (`h2Stmt_root`'s `hG`).
- `HelloRootBase`: `HelloRootPrem`'s fields but `W2`, `X2`, `Wc`, `G` and the premises on them (`x2_off`, `hXr`,
  `hP`); `h2`'s side a
  parameter, `H2Rt.ms2H` at `toPrem`.
- `HelloRootBase.toPrem`, `h0W_I`, `toPrem_X2`/`_G`/`_Wc`: in `A64HelloRootInstW` (they need `WcRootI`, which imports
this module).
- `hW2_I`: `OPremH.hW2` at `W2I` (`HelloW2.hW2H`, no premise).
- `hWX_I`: `H1GAH0.hWX` at these choices (at a state writing off the arena, `HelloW2.w2H_of_wsh`; `X2I` by
  `RootWX.hWX_W2H`).
- `wn_GJ1RH`: the pinned ghost's frame condition leaves `.data`/`pinned` unmapped.
- `c0S_I`: `C0S.c0S` placed at every state, not a return, its consumer facts (at the root's immediates `immsH`;
  the base no longer carries a `wc_main` control: hello's `wc_main` is entered at level 1).
- The base's sizes are raw (`ls`), every use at `ls0T ls`; main's frame is one `frM : Frame` (`toPrem`'s
  `frM := fun _ => B.frM`).
- `hstat_tablesOf`, `hstat_elf`: `toPrem`'s `hstat` by `rfl` at the link tables and at an ELF-read layout;
  `har_W`: the base's `har` at its arena parameter `arW`, from `CtrZ`.
-/
import Spike.Lib.A64HelloRootPrem
import Spike.Lib.A64HelloRootHP
import Spike.Lib.A64HelloRootWX
import Spike.Lib.A64HelloW2Weak
import Spike.Lib.A64HelloH2Inv
import Spike.Lib.A64HelloH2Rt
import Scc.Cert.Elf

namespace Spike.Lib.A64.HelloPh

variable {asm : String}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl)
open Spike.Lib.A64.Flow.HelloWc (WcPreWH WcSp0WH wARH WcCtxH)
open Spike.Lib.A64.Flow.Ret0 (CallerCells)
open Spike.Lib.A64.Alloc (Call AllocW)
open Spike.Lib.HelloHMid (BoxPureH BoxMH CloneMidH slWsH)
open Spike.Lib.HelloPreA (clonePcH)
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.A64.Rt.PreChild (r1Of)
open Spike.Lib.A64.Flow.HelloWc (tH)

/-- **The third level** at the box's labels (B8-W2H): no frames and `A64HelloW2H.W2H` at `ntA`,
`helloSrc`, `ClH`, the level-1 placement and sizes (`Wf` at the empty context, the twice extended placement
`lbl2H` and sizes `updN (updN lsize l n) l' n'`, so `OPremH.hW2` is `HelloW2.hW2H`). -/
abbrev W2I (L : RuntimeLayout) (ar : Spike.Lib.Arena) (Dt : State → Prop) (Ctx : Spike.Lib.FragS isaLSE2) (lbl : Lbl)
    (lsize : Spike.Lib.A64Consumer.Lsize) (l : WeakMem.AllocLabel) (b n : Nat) (l' : WeakMem.AllocLabel) (b' n' : Nat) :
    Spike.Lib.FragS isaLSE2 := fun s c fs =>
  fs = [] ∧ Spike.Lib.A64.HelloW2.W2H L.Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L (Spike.Lib.A64.Rt.Reserve.ntA L.lab)) ar
    Spike.Lib.HelloSrc.helloSrc Dt (Spike.Lib.A64.WriteAb.Ab L.lab) (ClH L)
    (Spike.Lib.A64.HelloWf.AcH L.lab Spike.Lib.A64.Flow.Worker.Hello.Child.pfxM) Ctx lbl lsize l b n l' b' n' s c fs

/-- **The fence's extra fact** at the box's labels: `X2H` at the take site, `lbl2H` and the level's sizes. -/
abbrev X2I (L : RuntimeLayout) (lbl : Lbl) (lsize : Spike.Lib.A64Consumer.Lsize) (l : WeakMem.AllocLabel) (b n : Nat)
    (l' : WeakMem.AllocLabel) (b' n' : Nat) : Spike.Lib.FragS isaLSE2 :=
  Spike.Lib.HelloH2Inv.X2H L (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL) L.endPc (lbl2H lbl l b l' b')
    (Spike.Lib.A64ConsumerA.updN (Spike.Lib.A64ConsumerA.updN lsize l n) l' n')

/-- **The level's extra fact at the clone**: the child's stack private. -/
abbrev WcI (L : RuntimeLayout) : Spike.Lib.Frag isaLSE2 := fun s _ => Spike.Lib.A64.Flow.Ret0.StackM (r1Of L.lab) s.st.1

/-- **`H1GAH0.hWX` at the instance's choices**: the start's level at main's frame, at a state writing off the
arena, is the third level (`HelloW2.w2H_of_wsh`), and `X0TH` at the take site the fence's extra fact
(`RootWX.hWX_W2H`'s second half). -/
theorem hWX_I {L : RuntimeLayout} {ar : Spike.Lib.Arena} {Dt : State → Prop} {Ctx : Spike.Lib.FragS isaLSE2}
    {lbl : Lbl} {lsize : Spike.Lib.A64Consumer.Lsize} {frM : Spike.Lib.Ctl → TermRun.Frame} {l : WeakMem.AllocLabel}
    {b n : Nat} {l' : WeakMem.AllocLabel} {b' n' : Nat} :
    ∀ c0 cA, Spike.Lib.A64.Flow.WakeWc.MidG (Spike.Lib.HelloHMid.SBH l' b' (slWsH l)) c0 cA → ∀ s c,
      Spike.Lib.A64.HelloPh.StartWf.WSH L (Spike.Lib.A64.Rt.Reserve.ntA L.lab) ar Spike.Lib.HelloSrc.helloSrc Dt
        (ClH L) Ctx (lbl2H lbl l b l' b') lsize (frM c0)
        (Spike.Lib.A64.HelloPh.Ti2.X0TH L (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL)) s c →
      Spike.Lib.A64.HelloW2.OffW ar s →
      W2I L ar Dt Ctx lbl lsize l b n l' b' n' s c [] ∧ X2I L lbl lsize l b n l' b' n' s c [] :=
  fun c0 cA hM s c h hoff => ⟨⟨rfl, Spike.Lib.A64.HelloW2.w2H_of_wsh h hoff⟩,
    (Spike.Lib.A64.HelloPh.RootWX.hWX_W2H (Ctx := Ctx) L.endPc _ _ c0 cA hM s c h).2⟩

/-- **`OPremH.hW2` at the instance's level** (`HelloW2.hW2H`, no premise): `SFactsACH` at every state of `W2I`, at
the twice extended placement `lbl2H` and sizes `updN (updN lsize l n) l' n'`, for any `rd`, `G`, fragment `J`. -/
theorem hW2_I {L : RuntimeLayout} {ar : Spike.Lib.Arena} {Dt : State → Prop} {Ctx : Spike.Lib.FragS isaLSE2}
    {lbl : Lbl} {lsize : Spike.Lib.A64Consumer.Lsize} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
    {J : Spike.Lib.A64ConsumerS.InvS} :
    ∀ l b n l' b' n' s c fs, W2I L ar Dt Ctx lbl lsize l b n l' b' n' s c fs →
      Spike.Lib.A64ConsumerA.SFactsACH L.Λ (Spike.Lib.A64.PhRec.μ L) Spike.Lib.HelloSrc.helloSrc rd G
        (fun s _ => ownGH L (Spike.Lib.A64.Rt.Reserve.ntA L.lab) s) ar J (lbl2H lbl l b l' b')
        (Spike.Lib.A64ConsumerA.updN (Spike.Lib.A64ConsumerA.updN lsize l n) l' n') s c fs Dt
        (Spike.Lib.A64.WriteAb.Ab L.lab) (ClH L)
        (Spike.Lib.A64.HelloWf.AcH L.lab Spike.Lib.A64.Flow.Worker.Hello.Child.pfxM) :=
  fun l b n l' b' n' s c fs h =>
    Spike.Lib.A64.HelloW2.hW2H _ _ _ _ _ _ _ _ _ _ _ _ l b n l' b' n' s c fs h.2

/-- **`HelloRootPrem`'s base**: its fields but the third level's choices and the premises on them (see the module
doc). The allocator's arena is the parameter `ar`
(`toPrem` fixes it to wake's `WakeOD.arW`). `h2`'s memory side is the parameter `ms2` at the level's sizes (`toPrem`
fixes it to `H2Rt.ms2H`, the side the runtime fields are proved at). -/
structure HelloRootBase (L : RuntimeLayout) (lbl : Lbl) (ar : Spike.Lib.Arena)
    (ms2 : Spike.Lib.A64Consumer.Lsize → WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat →
      List TermRun.Frame → Spike.Lib.MemSide isaLSE2) : Type where
  hp : L.prog = SccCode.helloProg
  hlo : L.Λ.code.lo = lo
  hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName
  hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x
  hsite : (Spike.Lib.A64.PhRec.μ L).site .take = some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat
  /-- `.rodata` off the stack pool (wake's `WakeOSide.hro_W`, A1 of any
  `PlaceW` output; `htiWH_place`'s `hro`). -/
  hro : L.Λ.rodata.Disjoint L.Λ.stackPool
  /-- The level after the allocation (wake's `WakeOPremW.W1W`). -/
  W1 : Spike.Lib.FragS isaLSE2
  /-- The arena's geometry: the counter off its cells, the box sizes
  (wake's `WakeOD.hok_W`, from `CtrZ`; `XchgWr.nodeW_wrC_rdX1`'s `har`). -/
  har : ar.OK
  /-- The start's level's debts (`StartWf.WSH`'s `Dt`; wake's `Dt`). -/
  Dt : State → Prop
  /-- The start's level's contexts (`WSH`'s `Ctx`; wake's `Ctx`). -/
  Ctx : Spike.Lib.FragS isaLSE2
  /-- The start's sizes, raw (wake's `ls0`): every use is at `WakeLoadT.ls0T ls` (`WSH`'s `lsize`, `W2I`, `X2I`),
  as `H2Rt.ms2H`, `HelloRootO.helloDR` and the level-1 sides take it, so the sizes agree by `rfl`. -/
  ls : Spike.Lib.A64Consumer.Lsize
  /-- main's frame (`WSH`'s `frM` at every `wc_main` control; `helloDR`'s `frM`, at hello's run
  `HelloRdCf.frH c0S.env`). -/
  frM : TermRun.Frame
  /-- The memory side the box's landing is stated at, per rodata's
  allocation (wake's `wake_h1` parameter `ms0`; hello's box lands in `h1`'s
  segment, so the instance is `h1`'s side at no frames). -/
  msB : WeakMem.AllocLabel → Nat → Nat → Spike.Lib.MemSide isaLSE2
  /-- The box's frame condition (wake's `wake_h1` parameter `F0`). -/
  F0 : MachineData → Prop
  /-- `h2`'s kernel at no frames (wake's `ms1W`'s `K`, by `rfl` there). -/
  hK2 : ∀ l b n l' b' n', Fresh2H ar lbl l b n l' b' n' → (ms2 ls l b n l' b' n' []).K = some Scc.Sem.A64.abi
  /-- `h2`'s publication at no frames (wake's `ms1W`'s `pub`). -/
  hpub2 : ∀ l b n l' b' n', Fresh2H ar lbl l b n l' b' n' → (ms2 ls l b n l' b' n' []).pub
  /-- The box call's premises carry from `msB` to `h2`'s side (wake's
  `wake_h1` premise `hokb`, `WakeBoxW.okb_ms1`). -/
  hokb : ∀ l b n l' b' n', Fresh2H ar lbl l b n l' b' n' →
    ∀ q : Call, q.OKB (msB l b n) L.lab → q.OKB (ms2 ls l b n l' b' n' []) L.lab
  /-- `h2`'s arena geometry `msB`'s (wake's `wake_h1` premise `hg`, `arW`'s
  geometry). -/
  hg : ∀ l b n l' b' n', Fresh2H ar lbl l b n l' b' n' →
    (ms2 ls l b n l' b' n' []).heap = (msB l b n).heap ∧
      (ms2 ls l b n l' b' n' []).cells = (msB l b n).cells ∧
      (ms2 ls l b n l' b' n' []).off = (msB l b n).off ∧
      (ms2 ls l b n l' b' n' []).units = (msB l b n).units
  /-- The runtime's words separated at the reserve's counter (wake's
  `StartPlaceLy.wsep_W`). -/
  hs : Spike.Lib.A64.WakePh.WSep L (Spike.Lib.A64.Rt.Reserve.ntA L.lab)
  /-- The second stack in the pool (wake's `StartPlaceLy.hsub1_W`, A13's data
  part). -/
  hsub : (r1Of L.lab).Sub L.Λ.stackPool
  /-- The second TCB's words mapped (wake's `LdFacts`; `hti_H`'s `hmF`). -/
  hmF : ∀ a ∈ Spike.Lib.A64.Rt.Ti.tiAddrs (tH L.lab),
    Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 L.Λ) true ⟨a, 8⟩ = true
  /-- The second TCB's words off the owned words (`hti_H`'s `hnoF`). -/
  hnoF : ∀ b ∈ Spike.Lib.A64.Rt.Ti.tiAddrs (tH L.lab), ∀ j w,
    (⟨b, 8⟩, w) ∉ own2bH L (Spike.Lib.A64.Rt.Reserve.ntA L.lab) j
  /-- The second TCB's words off the arena (wake's `StartH0Ti.offW_arW`). -/
  hoffT : ∀ b ∈ Spike.Lib.A64.Rt.Ti.tiAddrs (tH L.lab),
    ¬ (ar.heap ≤ b.toNat ∧ b.toNat < ar.heap + 16 * ar.cells) ∧ (⟨b, 8⟩ : Loc) ≠ ar.ctrLoc
  /-- The stack lock off the arena (wake's `offW_arW _ lock_mem`). -/
  hoffL : ¬ (ar.heap ≤ L.lockA.toNat ∧ L.lockA.toNat < ar.heap + 16 * ar.cells) ∧
    (⟨L.lockA, 8⟩ : Loc) ≠ ar.ctrLoc
  /-- The stack cursor off the arena (wake's `offW_arW _ next_mem`). -/
  hoffX : ¬ (ar.heap ≤ L.nextA.toNat ∧ L.nextA.toNat < ar.heap + 16 * ar.cells) ∧
    (⟨L.nextA, 8⟩ : Loc) ≠ ar.ctrLoc

namespace HelloRootBase

variable {asm : String}

section ToPrem

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : Spike.Lib.PlaceW pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat) (E : Scc.Sem.Entry)

set_option hygiene false in
local notation "IH" => Spike.Lib.A64.HelloPh.C0S.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hpw IH

set_option hygiene false in
local notation "LB" => Spike.Lib.WakeLoadT.L0T (Ly).Λ

set_option hygiene false in
local notation "AW" => Spike.Lib.WakeOD.arW hpw IH

open Spike.Lib.WakeLoadT (ls0T)

/-- **The pinned ghost's frame condition leaves `.data` and `pinned` unmapped**: `GJ1RH`'s `wcF … (FS …)` carries
`FS`'s `WordsNoneP` (whose private words include `.data` and `pinned`). -/
theorem wn_GJ1RH {lbl1 : Lbl} {lr : WeakMem.AllocLabel} {R : Spike.Lib.Region} {F : MachineData → Prop}
    {J1} {t : UInt64}
    (hG : Spike.Lib.A64.HelloPh.RootHP.GJ1RH (Ly) lbl1 lr R F J1 t) :
    ∀ m, F m → Spike.Lib.DmemPriv.WordsNoneP (Ly).Λ m.dmem := by
  obtain ⟨-, v, m1, σ1, -, hF⟩ := hG
  subst hF
  exact fun m h => h.1.1

/-- **`C0S.c0S`'s placement, control shape and consumer facts** (`C0S`, at the root's immediates `immsH`,
whose `me` is `tcb0`: `immsH_start`; wake's `hc0`, `hctl`, `hC0` at `c0W`). -/
theorem c0S_I :
    (∀ s, Spike.Lib.A64ConsumerS.PlacedSE (Ly).Λ (LB) s Spike.Lib.A64.HelloPh.C0S.c0S []) ∧
      ((∀ a, Spike.Lib.A64.HelloPh.C0S.c0S.term ≠ .ret a) ∧
        Spike.Lib.A64.WakeWf.RunWf Spike.Lib.HelloSrc.helloSrc Spike.Lib.A64.HelloPh.C0S.c0S []) ∧
      Spike.Lib.A64Consumer.CFacts (Ly).Λ (LB) Spike.Lib.A64.HelloPh.C0S.c0S :=
  ⟨Spike.Lib.A64.HelloPh.C0S.placedSE_c0S (Spike.Lib.A64.HelloPh.C0S.immsH_start Λ0 i0),
    Spike.Lib.A64.HelloPh.C0S.c0S_ctl,
    Spike.Lib.A64.HelloPh.C0S.cfacts_c0S (Spike.Lib.A64.HelloPh.C0S.immsH_start Λ0 i0)⟩

/-- **`toPrem`'s `hstat` at the placement's link tables**: the static link places no label (`rfl`, for every
configuration and output; wake's `WakeFinalCAO.hstat_cert` at its certificate). -/
theorem hstat_tablesOf (cfg : Scc.Cert.PlaceOK.Config) (o : Scc.Cert.PlaceOK.A64.Out) :
    (Scc.Cert.PlaceOK.A64.tablesOf cfg o).Λ.static = fun _ => none := rfl

/-- **`toPrem`'s `hstat` at a layout read from a linked ELF** (`ElfLayout.toLayout`, the binding instance's
layout as wake's `WakeLinkedA64`): no static placement, `rfl`. -/
theorem hstat_elf (e : Scc.Cert.Elf.ElfLayout) : e.toLayout.static = fun _ => none := rfl

/-- **The base's `har` at the arena `arW`**: the arena's geometry from the counter's zeroed item (`CtrZ`, a fact of
the emitted sections; wake's `WakeOD.hok_W`, by `Rt.ArenaW.arOf_ok`, as `Arena.OK` reads neither `newOk` nor
`pub`). -/
theorem har_W (hc : Spike.Lib.A64.Rt.CtrZ o) : (AW).OK :=
  let h := Spike.Lib.A64.Rt.ArenaW.arOf_ok (Spike.Lib.PlaceW.link IH hpw) hc
  ⟨h.ctr_out, h.units, h.off, h.units_lt, h.cells_lt, h.ctr_lt⟩

end ToPrem

end HelloRootBase

end Spike.Lib.A64.HelloPh

/-- info: 'Spike.Lib.A64.HelloPh.hWX_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.hWX_I

/-- info: 'Spike.Lib.A64.HelloPh.hW2_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.hW2_I

/-- info: 'Spike.Lib.A64.HelloPh.HelloRootBase.c0S_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.HelloRootBase.c0S_I

/-- info: 'Spike.Lib.A64.HelloPh.HelloRootBase.hstat_tablesOf' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.HelloRootBase.hstat_tablesOf

/-- info: 'Spike.Lib.A64.HelloPh.HelloRootBase.hstat_elf' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.HelloRootBase.hstat_elf

/-- info: 'Spike.Lib.A64.HelloPh.HelloRootBase.har_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.HelloRootBase.har_W
