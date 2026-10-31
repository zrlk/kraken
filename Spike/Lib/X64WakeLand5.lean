/-
**`inv0G` from a segment to the heap abort** (wake.w, x86-64; the twin of
`Spike/Lib/A64WakeLand5.lean`, with `StartH0B`'s `W0S`, `QabW` and
`takeCKS_iff`): any pre-lift segment inside `WSX` under the take
`PhRec.K` at `msBotX … E []`, ending at `wc_main`'s heap-abort exit
(`QabX`), puts its entry pairs in `h0`'s invariant `X64WakeFinal.inv0G` at
the frames `[]`, for any precondition `P` (the counter add's tail, the
start).

- `segWS_mono_W`, `segWS_mono_K` (generic): `SegWS` inside a weaker
  predicate, and under outside moves agreeing at its states.
- `takeCKS_iff`: the take at `aW` is `PhRec.K` at `X0W`'s states (`aW` is
  the take site's label, the site's range there main's stack, `r0Of =
  rS0`; no `clone` refusal off the clone's pc).
- `W0S`: `W0` at the start's marks and `ownGXW` (the heap abort's level),
  `WSX` at the frames `[]` by definition.
- `QabX`: `StartH0X.wake_start_wc_h0X`'s exit at `msBotX … E []`, without
  its `U r1Of` conjunct.
- `inv0_of_habW`: lift at `[]` (`SegWS.liftS` into `W0S`), the heap abort
  closed (`StartH0C.wake_hab_closed`), the take as `TakeCKS`
  (`takeCKS_iff`), `W0S` as `W0W` (`marks_target`), then `gfpS_of_segWS`.

**Where x86-64 differs from AArch64**:
- the root is `X64WakeFinal`'s (`inv0G` at `msBotX`; A64 `WakeRoot.inv0R`
  at `msBot`), generic in `cT` and `Ctx`; the level owns `ownGXW` (`WSX`,
  A64 `WS` at `ownG`);
- the exit's start control `c0` inside `JW` is generic, with its box shape,
  facts and placement premises (`hbx`, `hc0`, `hpl0`; A64 at `c0W`, its
  placement the theorem `WakeImmsC0.placedSE_c0WW`, no x86-64 producer);
- the heap abort path's `ownG` → `ownGXW` lift `StartH0C.HabLft` is carried
  (`hlft`; A64's level owns `ownG`, none needed);
- the loader's fact is `hpa : cellsOf certAsm = some outLit.prog` (A64 two
  `textProgram` parses); the program is `X64WakeParse.outLit_prog`;
- the region is `wR (RS wcLsw v) wcD` and the pinned word
  `TP (tpOf (tcbS (Ly)))` (A64 `wR (swR v (-384) 0) 336`, `pinA + 8`);
- `SegWS.mono_W`/`mono_K` are restated here under new names (A64's live in
  `A64WakeStartH0B`).
-/
import Spike.Lib.X64WakeFinal
import Spike.Lib.X64WakeStartH0C
import Spike.Lib.X64WakeAWSite
import Spike.Lib.X64WakeRootP
import Spike.Lib.X64GfpS
import Spike.Lib.X64WakeOwnImp

namespace Spike.Lib.X64.WakePh.Land5

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Entry)
open Scc.Sem.X64 (pcOf cellsOf)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64ConsumerS (PlacedSE)
open Spike.Lib.X64ConsumerA (TakeCKS)
open Spike.Lib.X64 (At)
open Spike.Lib.X64.Flow.Ret0 (tpOf)
open Spike.Lib.X64.Flow.WakeM (wR wF wJ0 wNC)
open Spike.Lib.X64.Flow.WakeWc (wX)
open Spike.Lib.X64.WakeWf (DtW W0 RunWf X0W)
open Spike.Lib.X64.WakePh.MainGlue (FS JS RS tcbS)
open Spike.Lib.X64.WakePh.StartFacts (wcD wcLsw)
open Spike.Lib.X64.WakePh.StartWf (pfxM)
open Spike.Lib.X64.WakePh.StartH0 (C0Box)
open Spike.Lib.X64.KeepTP (TP)
open Spike.Lib.X64.Rt.Reserve (ntA)
open Spike.Lib (FragS Frag MemSide SegW SegWS PlaceWX)
open Spike.Lib.X64WakeLoadT (L0T ls0T)
open Spike.Lib.X64WakeT1 (wakeSrc)
open Spike.Lib.X64WakeParse (certAsm)
open Spike.Lib.X64WakeFinal (msBotX inv0G)
open SccCertificate (outLit)

section Gen

variable {I : ISA} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat}

/-- `SegWS` inside a weaker predicate. -/
theorem segWS_mono_W {W W' : FragS I} {K : I.State → I.State → Prop} {ms : List TermRun.Frame → MemSide I}
    {P Q : FragS I} (h : SegWS W K p lbl ms P Q) (hW : ∀ s c fs, W s c fs → W' s c fs) : SegWS W' K p lbl ms P Q :=
  let ⟨i, hs, hw, ho⟩ := h
  ⟨i, hs, fun s c fs h => hW s c fs (hw s c fs h), ho⟩

/-- `SegWS` under outside moves `K'` that move the predicate's states as
`K` does. -/
theorem segWS_mono_K {W : FragS I} {K K' : I.State → I.State → Prop} {ms : List TermRun.Frame → MemSide I}
    {P Q : FragS I} (h : SegWS W K p lbl ms P Q) (hK : ∀ s c fs, W s c fs → ∀ s', K' s s' ↔ K s s') :
    SegWS W K' p lbl ms P Q :=
  let ⟨i, hs, hw, ho⟩ := h
  ⟨i, hs, hw, fun s c fs h =>
    ⟨fun hn => (ho s c fs h).1 fun s' hk => hn s' ((hK s c fs (hw s c fs h) s').2 hk),
      fun s' hk => (ho s c fs h).2 s' ((hK s c fs (hw s c fs h) s').1 hk)⟩⟩

end Gen

section Take

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

/-- **The take at `aW` is `PhRec.K` at `X0W`'s states**: `aW` is the take
site's label (`aW_site`), the site's range there main's stack (`X0W`,
`r0Of = rS0`), and no `clone` refusal off the clone's pc. -/
theorem takeCKS_iff {asm : Scc.Sem.X64.Asm} (hpa : cellsOf asm = some o.prog) (E : Entry) {s s' : State}
    (hx : X0W (Ly) (Spike.Lib.X64WakeOSide.aW hp i E) s) :
    TakeCKS (Spike.Lib.X64WakeOSide.aW hp i E) (Spike.Lib.X64.WakeOD.ClW hp i) s s' ↔
      Spike.Lib.X64.PhRec.K (Ly) (Spike.Lib.X64.Rt.rS0 (Ly)) s s' := by
  have haW := Spike.Lib.X64WakeOSide.aW_site hp i hpa E
  have hr0 : Spike.Lib.X64.Rt.Ti2.r0Of (Ly).lab = Spike.Lib.X64.Rt.rS0 (Ly) := Spike.Lib.X64.WakePh.RootP.r0Of_rS0
  obtain ⟨hcl, hsr⟩ := hx
  constructor
  · rintro (⟨hpc, pm, rfl⟩ | ⟨⟨hc, -⟩, -⟩)
    · have hr := (hsr (congrArg (fun x : Int64 => x.toBitVec.toNat) hpc)).1
      exact ⟨hpc.trans haW, pm, by rw [hr, hr0]⟩
    · exact (hcl hc).elim
  · rintro ⟨hpc, pm, rfl⟩
    have hpa' : s.st.2 = Spike.Lib.X64WakeOSide.aW hp i E := hpc.trans haW.symm
    have hr := (hsr (congrArg (fun x : Int64 => x.toBitVec.toNat) hpa')).1
    exact .inl ⟨hpa', pm, by rw [hr, hr0]⟩

end Take

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 outLit) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (cT : Entry → Loc) (ls0 : Entry → Lsize) (Ctx : Entry → FragS isa) (frM : Entry → TermRun.Frame)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

/-- **The level before the allocation at the start's marks** (`PhRec.μ`):
`W0` at the root's choices and `ownGXW`, the heap abort's fragment
(`StartH0C.wake_hab_closed`); `WSX` at the frames `[]` by definition,
`W0W` by `marks_target`. -/
abbrev W0S (E : Entry) : FragS isa :=
  W0 (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) (Spike.Lib.X64.WakePh.ownGXW (Ly) (ntA (Ly).lab))
    (Spike.Lib.X64.WakeOD.arW hp i) wakeSrc DtW (Spike.Lib.X64.WriteAb.Ab (Ly).lab) (Spike.Lib.X64.WakeOD.ClW hp i)
    (Spike.Lib.X64.ThreadsAb.Ac (Ly).lab pfxM) (Ctx E) (L0T (Ly).Λ) (ls0T (ls0 E)) (frM E)
    (X0W (Ly) (Spike.Lib.X64WakeOSide.aW hp i E))

/-- **`wake_start_wc_h0X`'s exit at the root's memory side** (without its
`U r1Of` conjunct): `wc_main`'s heap abort call (`wX .abort`) in
`wc_main`'s region below the start control `c0`'s entry, main's thread
pointer kept. -/
def QabX (c0 : Ctl) (E : Entry) : Frag isa := fun s c => ∃ v m0 σC,
  At (Ly).exe (Ly).endPc (wR (RS wcLsw v) wcD)
    (wF (RS wcLsw v) wcD (FS (Ly) (Spike.Lib.X64.Rt.rS0 (Ly)) wcLsw 0#64 v) m0 σC)
    (wX (msBotX hp i cT ls0 Ctx frM E []) (Ly).lab (wR (RS wcLsw v) wcD)
      (wJ0 (wNC (Ly).lab (JS (Ly) 0#64 c0)).J σC) .abort) s c ∧
  TP (tpOf (tcbS (Ly))) s

set_option hygiene false in
/-- The start's level at `ownGXW` at entry `E`. -/
local notation "WSE" => Spike.Lib.X64.WakePh.WSX (Ly) (ntA (Ly).lab) (Spike.Lib.X64.WakeOD.arW hp i) wakeSrc DtW
  (Spike.Lib.X64.WakeOD.ClW hp i) (Ctx E) (L0T (Ly).Λ) (ls0T (ls0 E)) (frM E)
  (X0W (Ly) (Spike.Lib.X64WakeOSide.aW hp i E))

/-- **A segment to the heap abort gives `inv0G` at `[]`**: from `P` inside
`WSX` under `PhRec.K` at `msBotX … E []` to `QabX`, every `P` pair is in
`inv0G … E` at the frames `[]`. -/
theorem inv0_of_habW (E : Entry) {c0 : Ctl} (hpa : cellsOf certAsm = some outLit.prog)
    (hlo : Λ0.code.lo = Spike.Lib.X64.WakePh.lo)
    /- the start control's box shape, facts and placement -/
    (hbx : C0Box c0) (hc0 : (∀ a, c0.term ≠ .ret a) ∧ RunWf wakeSrc c0 [])
    (hpl0 : ∀ s, PlacedSE (Ly).Λ (L0T (Ly).Λ) s c0 [])
    /- the heap abort path's `ownG` → `ownGXW` lift -/
    (hlft : Spike.Lib.X64.WakePh.StartH0C.HabLft (Ly))
    {P : Frag isa}
    (h : SegW (WSE) (Spike.Lib.X64.PhRec.K (Ly) (Spike.Lib.X64.Rt.rS0 (Ly))) wakeSrc (L0T (Ly).Λ)
      (msBotX hp i cT ls0 Ctx frM E []) P (QabX hp i cT ls0 Ctx frM c0 E)) :
    ∀ s c, P s c → inv0G hp i cT ls0 Ctx frM E s c [] := by
  have hax : (Spike.Lib.X64WakeOSide.aW hp i E).toBitVec.toNat =
      ((Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat := by
    rw [Spike.Lib.X64WakeOSide.aW_site hp i hpa E]
  have hC := Spike.Lib.X64.WakePh.StartH0C.wake_hab_closed hp i (E := E) (asm := certAsm)
    (rd := fun _ => True) (G := Spike.Lib.X64WakeOG.gW hp i (cT E))
    (own := fun s _ => Spike.Lib.X64.WakePh.ownGXW (Ly) (ntA (Ly).lab) s)
    (I := Spike.Lib.X64ConsumerA.I2 (Spike.Lib.X64.WakeOD.arW hp i) (L0T (Ly).Λ) (ls0T (ls0 E))
      (fun _ _ _ => False) (Spike.Lib.X64.WakeH1Inv.inv1W certAsm hp i E (cT E) DtW (Ctx E) (ls0 E)))
    (p := wakeSrc) (L0 := L0T (Ly).Λ) (ls := ls0T (ls0 E)) (Ctx := Ctx E) (ls0 := ls0T (ls0 E)) (frM := frM E)
    hpa Spike.Lib.X64WakeParse.outLit_prog hlo hax hbx hc0 hpl0 hlft
  have hS : SegWS (Spike.Lib.X64.WakeOPremW.W0W certAsm hp i E DtW (Ctx E) (ls0 E) (frM E))
      (TakeCKS (Spike.Lib.X64WakeOSide.aW hp i E) (Spike.Lib.X64.WakeOD.ClW hp i)) wakeSrc (L0T (Ly).Λ)
      (msBotX hp i cT ls0 Ctx frM E) (Frag.at P []) (fun _ _ _ => False) :=
    segWS_mono_W (segWS_mono_K (((Spike.Lib.SegWS.liftS (ms := msBotX hp i cT ls0 Ctx frM E)
      (W := W0S hp i ls0 Ctx frM E) [] h fun _ _ h => h).seq hC))
      fun s c fs hW s' => takeCKS_iff hp i hpa E hW.2.1) fun s c fs h => by
        unfold Spike.Lib.X64.WakeOPremW.W0W Spike.Lib.X64.WakeOD.AbW Spike.Lib.X64.WakeOD.AcW
        rw [Spike.Lib.X64.Flow.Worker.Wake.AbOffW.marks_target (Ly) hpa]; exact h
  exact fun s c hP => Spike.Lib.X64GfpS.gfpS_of_segWS hS s c [] ⟨hP, rfl⟩

end Place

end Spike.Lib.X64.WakePh.Land5

/-- info: 'Spike.Lib.X64.WakePh.Land5.segWS_mono_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Land5.segWS_mono_W

/-- info: 'Spike.Lib.X64.WakePh.Land5.segWS_mono_K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Land5.segWS_mono_K

/-- info: 'Spike.Lib.X64.WakePh.Land5.takeCKS_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Land5.takeCKS_iff

/-- info: 'Spike.Lib.X64.WakePh.Land5.inv0_of_habW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Land5.inv0_of_habW
