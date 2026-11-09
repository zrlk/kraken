/-
**hello's root premises from their base** (x86-64; twin of `Spike/Lib/A64HelloRootInst.lean`): the choices
`HelloRootPrem` leaves free that the h1/h2 chains fix, made once, and the named premises they discharge.

- `W2Ig`, `X2I`, `WcI`: the third level (no frames and `HelloW2.W2H`, the empty context, at any owned words `own`,
  `helloSrc`, `ClH`, the level-1 placement and sizes), the fence fact `X2H` at the take site and the level's sizes, the
  clone fact `StackM r1Of`.
- `HelloRootBase`: `HelloRootPrem`'s fields but `W2`, `X2`, `Wc`, `G` and the premises on them (`x2_off`, `hXr`,
  `hP`); `h2`'s side a parameter at the base's raw sizes.
- `hW2_I`: `OPremH.hW2` at `W2Ig own` (`HelloW2.hW2H`, no premise).
- `hWX_Ig`: `H1GAH0.hWX` at these choices, at any `own` (at a state writing off the arena,
  `HelloW2.w2H_of_wshg`; `X2I` by `RootWX.hWX_W2Hg`).
- `HelloRootBase.wn_GJ1RH`: the pinned ghost's frame condition leaves `.data`/`pinned` unmapped.
- `HelloRootBase.har_W`: the base's `har` at the arena `WakeOD.arW`, from `CtrZ`.
- The base's sizes are raw (`ls`), every use at `ls0T ls`; main's frame is one `frM : Frame`.

## Unlike AArch64

- The code is `helloCells` with labels by `codeLabel` (AArch64 `helloProg`, `codeOf`); `h2`'s kernel is
  `X64.abi`; the source is `X64HelloSrc.helloSrc`; the start's `clone` phase is x86-64's
  `Hello.ThreadsAb.AcH … StartWf.pfxM`.
- `hWX_Ig` is at the box's fence `QBH` (x86-64's `H1GAHG.hWX`; AArch64 `SBH`).
- The pinned ghost's frame condition is `wcF (RS helloLsw v) …` over the call's region, whose `FS`'s
  `WordsNoneP` sits one conjunct deeper (`h.1.1.1`; AArch64 `h.1.1`).
- The third level, `hW2_I` and `hWX_Ig` are generic in the owned words (`W2Ig`; AArch64's `W2I`, `hWX_I`: at
  `ownGH`); the root's are at `ownGHXW`.
- AArch64's `c0S_I`, `hstat_tablesOf` and `hstat_elf` are unused by the hello proof and have no twin here.
-/
import Spike.Lib.X64HelloRootPrem
import Spike.Lib.X64HelloRootHPD
import Spike.Lib.X64HelloRootWX
import Spike.Lib.X64HelloW2H
import Spike.Lib.X64WakeOD
import Spike.Lib.X64HelloImms

namespace Spike.Lib.X64.HelloPh

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (codeLabel)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl)
open Spike.Lib.X64.Alloc (Call)
open Spike.Lib.X64HelloHMid (slWsH)
open Spike.Lib.X64.Rt.PreChild (r1Of)
open Spike.Lib.X64.Flow.HelloWc (tH)

/-- **The third level at any owned words `own`** at the box's labels: no frames and `X64.HelloW2.W2H` at `own`,
`helloSrc`, `ClH`, the level-1 placement and sizes (`Wf` at the empty context, the twice extended placement `lbl2H`
and sizes `updN (updN lsize l n) l' n'`, so `OPremH.hW2` is `HelloW2.hW2H`). -/
abbrev W2Ig (own : Spike.Lib.X64Consumer.Own) (L : RuntimeLayout) (ar : Spike.Lib.Arena) (Dt : State → Prop)
    (Ctx : Spike.Lib.FragS isa) (lbl : Lbl) (lsize : Spike.Lib.X64Consumer.Lsize) (l : WeakMem.AllocLabel)
    (b n : Nat) (l' : WeakMem.AllocLabel) (b' n' : Nat) : Spike.Lib.FragS isa := fun s c fs =>
  fs = [] ∧ Spike.Lib.X64.HelloW2.W2H L.Λ (Spike.Lib.X64.PhRec.μ L) own
    ar Spike.Lib.X64HelloSrc.helloSrc Dt (Spike.Lib.X64.WriteAb.Ab L.lab) (ClH L)
    (Spike.Lib.X64.Hello.ThreadsAb.AcH L.lab Spike.Lib.X64.HelloPh.StartWf.pfxM) Ctx lbl lsize l b n l' b' n' s c fs

/-- **The fence's extra fact** at the box's labels: `X2H` at the take site, `lbl2H` and the level's sizes. -/
abbrev X2I (L : RuntimeLayout) (lbl : Lbl) (lsize : Spike.Lib.X64Consumer.Lsize) (l : WeakMem.AllocLabel)
    (b n : Nat) (l' : WeakMem.AllocLabel) (b' n' : Nat) : Spike.Lib.FragS isa :=
  Spike.Lib.X64HelloH2Inv.X2H L (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL) L.endPc (lbl2H lbl l b l' b')
    (Spike.Lib.X64ConsumerA.updN (Spike.Lib.X64ConsumerA.updN lsize l n) l' n')

/-- **The level's extra fact at the clone**: the child's stack private. -/
abbrev WcI (L : RuntimeLayout) : Spike.Lib.Frag isa := fun s _ =>
  Spike.Lib.X64.Flow.Ret0.StackM (r1Of L.lab) s.st.1

/-- **`H1GAH0.hWX` at the instance's choices, at any owned words `own`**: the start's level at main's frame
(`StartWf.WSHg own`), at a state writing off the arena, is the third level at `own` (`HelloW2.w2H_of_wshg`), and
`X0TH` at the take site the fence's extra fact (`RootWX.hWX_W2Hg`'s second half). -/
theorem hWX_Ig {own : Spike.Lib.X64Consumer.Own} {L : RuntimeLayout} {ar : Spike.Lib.Arena} {Dt : State → Prop}
    {Ctx : Spike.Lib.FragS isa} {lbl : Lbl} {lsize : Spike.Lib.X64Consumer.Lsize}
    {frM : Spike.Lib.Ctl → TermRun.Frame} {l : WeakMem.AllocLabel} {b n : Nat} {l' : WeakMem.AllocLabel}
    {b' n' : Nat} :
    ∀ c0 cA, Spike.Lib.X64.Flow.WakeWc.MidG (Spike.Lib.X64HelloHMid.QBH l' b' (slWsH l)) c0 cA → ∀ s c,
      Spike.Lib.X64.HelloPh.StartWf.WSHg own L ar Spike.Lib.X64HelloSrc.helloSrc Dt
        (ClH L) Ctx (lbl2H lbl l b l' b') lsize (frM c0)
        (Spike.Lib.X64.HelloPh.Ti2.X0TH L (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL)) s c →
      Spike.Lib.X64.HelloW2.OffW ar s →
      W2Ig own L ar Dt Ctx lbl lsize l b n l' b' n' s c [] ∧ X2I L lbl lsize l b n l' b' n' s c [] :=
  fun c0 cA hM s c h hoff => ⟨⟨rfl, Spike.Lib.X64.HelloW2.w2H_of_wshg h hoff⟩,
    (Spike.Lib.X64.HelloPh.RootWX.hWX_W2Hg (Ctx := Ctx) L.endPc _ _ c0 cA hM s c h).2⟩

/-- **`OPremH.hW2` at the instance's level** (`HelloW2.hW2H`, no premise): `SFactsACH` at every state of `W2Ig own`
(e.g. `W2Ig ownGHXW`), at the twice extended placement `lbl2H` and sizes `updN (updN lsize l n) l' n'`, for any `rd`,
`G`, fragment `J`. -/
theorem hW2_I {own : Spike.Lib.X64Consumer.Own} {L : RuntimeLayout} {ar : Spike.Lib.Arena} {Dt : State → Prop}
    {Ctx : Spike.Lib.FragS isa} {lbl : Lbl} {lsize : Spike.Lib.X64Consumer.Lsize} {rd : TermRun.Word → Prop}
    {G : Loc → Val → Prop} {J : Spike.Lib.X64ConsumerS.InvS} :
    ∀ l b n l' b' n' s c fs, W2Ig own L ar Dt Ctx lbl lsize l b n l' b' n' s c fs →
      Spike.Lib.X64ConsumerA.SFactsACH L.Λ (Spike.Lib.X64.PhRec.μ L) Spike.Lib.X64HelloSrc.helloSrc rd G
        (fun s _ => own s) ar J (lbl2H lbl l b l' b')
        (Spike.Lib.X64ConsumerA.updN (Spike.Lib.X64ConsumerA.updN lsize l n) l' n') s c fs Dt
        (Spike.Lib.X64.WriteAb.Ab L.lab) (ClH L)
        (Spike.Lib.X64.Hello.ThreadsAb.AcH L.lab Spike.Lib.X64.HelloPh.StartWf.pfxM) :=
  fun l b n l' b' n' s c fs h =>
    Spike.Lib.X64.HelloW2.hW2H _ _ _ _ _ _ _ _ _ _ _ _ l b n l' b' n' s c fs h.2

/-- **`HelloRootPrem`'s base**: its fields but the third level's choices and the premises on them (see the module
doc). The allocator's arena is the parameter `ar`. `h2`'s memory side is the parameter `ms2` at the level's
sizes. -/
structure HelloRootBase (L : RuntimeLayout) (lbl : Lbl) (ar : Spike.Lib.Arena)
    (ms2 : Spike.Lib.X64Consumer.Lsize → WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat →
      List TermRun.Frame → Spike.Lib.MemSide isa) : Type where
  hp : L.prog = SccCode.helloCells
  hlo : L.Λ.code.lo = lo
  hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName
  hlab : ∀ l x, codeLabel lo SccCode.helloCells l = some x → L.lab l = Int64.ofNat x
  hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat
  /-- `.rodata` off the stack pool (`hti_HOX`'s `hro`). -/
  hro : L.Λ.rodata.Disjoint L.Λ.stackPool
  /-- The arena's geometry: the counter off its cells, the box sizes. -/
  har : ar.OK
  /-- The start's level's debts (`StartWf.WSH`'s `Dt`). -/
  Dt : State → Prop
  /-- The start's level's contexts (`WSH`'s `Ctx`). -/
  Ctx : Spike.Lib.FragS isa
  /-- The start's sizes, raw: every use is at `WakeLoadT.ls0T ls`. -/
  ls : Spike.Lib.X64Consumer.Lsize
  /-- main's frame (`WSH`'s `frM` at every `wc_main` control). -/
  frM : TermRun.Frame
  /-- The memory side the box's landing is stated at, per rodata's allocation (hello's box lands in `h1`'s
  segment, so the instance is `h1`'s side at no frames). -/
  msB : WeakMem.AllocLabel → Nat → Nat → Spike.Lib.MemSide isa
  /-- The box's frame condition. -/
  F0 : MachineData → Prop
  /-- `h2`'s kernel at no frames. -/
  hK2 : ∀ l b n l' b' n', Fresh2H ar lbl l b n l' b' n' → (ms2 ls l b n l' b' n' []).K = some Scc.Sem.X64.abi
  /-- `h2`'s publication at no frames. -/
  hpub2 : ∀ l b n l' b' n', Fresh2H ar lbl l b n l' b' n' → (ms2 ls l b n l' b' n' []).pub
  /-- The box call's premises carry from `msB` to `h2`'s side. -/
  hokb : ∀ l b n l' b' n', Fresh2H ar lbl l b n l' b' n' →
    ∀ q : Call, q.OKB (msB l b n) L.lab → q.OKB (ms2 ls l b n l' b' n' []) L.lab
  /-- `h2`'s arena geometry `msB`'s. -/
  hg : ∀ l b n l' b' n', Fresh2H ar lbl l b n l' b' n' →
    (ms2 ls l b n l' b' n' []).heap = (msB l b n).heap ∧
      (ms2 ls l b n l' b' n' []).cells = (msB l b n).cells ∧
      (ms2 ls l b n l' b' n' []).off = (msB l b n).off ∧
      (ms2 ls l b n l' b' n' []).units = (msB l b n).units
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

namespace HelloRootBase

section ToPrem

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : Spike.Lib.PlaceWX pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "IH" => Spike.Lib.X64.HelloImms.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw IH

set_option hygiene false in
local notation "AW" => Spike.Lib.X64.WakeOD.arW hpw IH

/-- **The pinned ghost's frame condition leaves `.data` and `pinned` unmapped**: `GJ1RH`'s `wcF … (FS …)` carries
`FS`'s `WordsNoneP` (whose private words include `.data` and `pinned`). -/
theorem wn_GJ1RH {lbl1 : Lbl} {lr : WeakMem.AllocLabel} {R : Spike.Lib.Region} {F : MachineData → Prop}
    {J1 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop} {t : UInt64}
    (hG : Spike.Lib.X64.HelloPh.RootHP.GJ1RH (Ly) lbl1 lr R F J1 t) :
    ∀ m, F m → Spike.Lib.X64.DmemPriv.WordsNoneP (Ly).Λ m.dmem := by
  obtain ⟨-, v, m1, σ1, -, hF, -⟩ := hG
  subst hF
  exact fun m h => h.1.1.1

/-- **The base's `har` at the arena `arW`**: the arena's geometry from the counter's zeroed item (`CtrZ`, a fact of
the emitted sections; by `Rt.ArenaW.arOf_ok`, as `Arena.OK` reads neither `newOk` nor `pub`). -/
theorem har_W (hc : Spike.Lib.X64.Rt.CtrZ o) : (AW).OK :=
  let h := Spike.Lib.X64.Rt.ArenaW.arOf_ok (Spike.Lib.PlaceWX.link IH hpw) hc
  ⟨h.ctr_out, h.units, h.off, h.units_lt, h.cells_lt, h.ctr_lt⟩

end ToPrem

end HelloRootBase

end Spike.Lib.X64.HelloPh

/-- info: 'Spike.Lib.X64.HelloPh.hWX_Ig' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.hWX_Ig

/-- info: 'Spike.Lib.X64.HelloPh.hW2_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.hW2_I

/-- info: 'Spike.Lib.X64.HelloPh.HelloRootBase.wn_GJ1RH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.HelloRootBase.wn_GJ1RH

/-- info: 'Spike.Lib.X64.HelloPh.HelloRootBase.har_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.HelloRootBase.har_W
