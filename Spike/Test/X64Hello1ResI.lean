/-
**The landings' contexts' `CxLB` at an extended placement at a walk with
no allocation** (x86-64; plan b1's walk restriction): at a walk predicate
`T` holding at no allocation's `let` in the `rodata` block (e.g.
`TailAt2 p j` restricted to `TrNb`, the points after the block's only
allocation), a landings' context `CxOkH` has `CxLB` at a landing's
extended placement `upd L l b`, `updN ls l n` at `T` with no allocation
premise: `CxLB`'s two fields reading the walk (`hAW`, `hAb`) hold
vacuously there (`allocW2At_noNb`, `nbAb_noNb`), at the start's placement
(`setupCxLB_ofPreT`) and at the extended one (`cxLB_updT`).

- `cxLBT_ofCxOkH`: a context's `CxLB` at an extended placement at a walk
  with no allocation in `rodata`;
- `hello1_cxLBT`: at `hello1o`, at `rodata`'s walk restricted to `TrNb`;
- `resumeCx2T_ofCxOkH`: `H1RestXWT.hresL`'s field at `CxOkH` at a
  restriction with no allocation in `rodata` (`resumeCx2T_ofCxLB_noCall`
  at `cxLBT_ofCxOkH`'s `CxLB`);
- `hello1_restXT`: `hello1_final'`'s `H1RestXWT` at `TrNb (TailAt2 P1 j)`
  from the bottom keys' exits `hW` alone (`hello1_hbot`'s);
- `hello1_finalT`: `hello1_final'` with `HR` by `hello1_restXT`;
- `hello1_restXTW`, `hello1_finalTW`: the same at `hello1_hWBot` (`HR` closed;
  open: `OpenAWF`).
-/
import Spike.Test.X64Hello1Res
import Spike.Test.X64Hello1ResT
import Spike.Lib.LowerX64.NbNone
import Spike.Lib.LowerX64.ResumeCx2T
import Spike.Lib.LowerX64.H1InLandWT
import Spike.Test.X64Hello1HAW
import Spike.Test.X64Hello1HBot
import Spike.Test.X64Hello1TgOk
import Spike.Test.X64Hello1HsOf
import Spike.Test.X64Hello1FinalO
import Spike.Test.X64Hello1HWBot

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (swR FStable At BlkW ND okBlk)
open Spike.Lib.X64Consumer (noRetBlk)
open Spike.Lib.X64.Flow.Ret0
open Spike.Lib.X64.Flow.Ret0 (WcG CallerCells limA)
open Spike.Lib.X64.Rt (setupMC rS0 arOf swFSL)
open Spike.Lib.X64.WriteAb (Ab)
open Spike.Lib.LowerNode (FrOk2 ZBad setupWords2 compiled2 TailAt2 imms2Me addFreeT tailOf_addFree)
open Spike.Lib.AllocReach (Reach IN)
open Spike.Lib.X64.Flow.NewBuf (nbX)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The runtime's layout of the output at the compiler's immediates (`fnCode2OfP`'s). -/
local notation "LY0" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)

set_option hygiene false in
/-- The allocator's arena of the output. -/
local notation "Ar" => Spike.Lib.X64.Rt.arOf (lay2 Λ p)

set_option hygiene false in
/-- The output's code. -/
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs)

set_option hygiene false in
/-- The record's marks. -/
local notation "Mk" => Spike.Lib.X64.PhRec.μ (Ly)

set_option hygiene false in
/-- **`W2` at the record** at a placement `L`, `ls`, over `IN … J` (`H1OpenXW`'s). -/
local notation "W2R" J:max Dt:max L:max ls:max =>
  fun s c fs => W2 (lay2 Λ p) (Mk) p Spike.Lib.LowerNode.IsNum (G2 h p) (Spike.Lib.X64.PhRec.own (Ly))
    (Spike.Lib.X64.Rt.rS0 (Ly)) (Spike.Lib.X64.PhRec.Tk (Ly)) (Ar) (IN (Ar) (fun _ => none) (fun _ => 0) J) Dt
    (Spike.Lib.X64.WriteAb.Ab (Ly).lab) L ls s c fs

set_option hygiene false in
/-- **The rows' memory side at the record** at the nodes' abort `ab2` (`H1OpenXW`'s). -/
local notation "MSR" J:max L:max ls:max =>
  msOfAX (lay2 Λ p) (Mk) p Spike.Lib.LowerNode.IsNum (G2 h p) (fun s _ => Spike.Lib.X64.PhRec.own (Ly) s) (Ar)
    (IN (Ar) (fun _ => none) (fun _ => 0) J) (ab2 p (Ly).lab) L ls

set_option hygiene false in
/-- The take's outside moves. -/
local notation "KT" => TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))

set_option hygiene false in
/-- **`CxLB` at the record** at a placement `L0`, `ls0` for the `j`th
compiled block's code facts at the return address `ra`, at a walk `T`. -/
local notation "CXT" J:max Dt:max L0:max ls0:max hd:max T:max =>
  CxLB (lay2 Λ p) (Mk) p Spike.Lib.LowerNode.IsNum (G2 h p) (Spike.Lib.X64.PhRec.own (Ly)) (rS0 (Ly))
    (Spike.Lib.X64.PhRec.Tk (Ly)) (Ar) (IN (Ar) (fun _ => none) (fun _ => 0) J) Dt (Ly).lab (KT) (Ly).exe
    (Ly).endPc (MSR J L0 ls0) L0 ls0 (fnCode2OfPMe hp h Λ j d hd).lcx (fnCode2OfPMe hp h Λ j d hd).fr
    (CdCLE OP (Spike.Lib.X64.PhRec.okPc LY0) (Spike.Lib.X64.PhRec.ph LY0) (LY0).lab (Int64.ofBitVec ra))
    ((fnCode2OfPMe hp h Λ j d hd).Bl ra) (imms2Me Λ p) T (RetLk d.retTy)

section Assembled

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  {sizes : List Nat} {labelOffs : List (String × Nat)}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)

/-- **A landings' context's `CxLB` at an extended placement at a walk with
no allocation** (no allocation premise): at a walk `T` holding at no
allocation's `let` when the block is `rodata` (`hT`), the context's
`SetupCxLB` at `T` from its setup call's premises (`setupCxLB_ofPreT`,
the walk-reading fields vacuous: `allocW2At_noNb`, `nbAb_noNb`), moved to
the extended placement `upd L l b`, `updN ls l n` at `T` (`cxLB_updT`,
the same fields vacuous). -/
theorem cxLBT_ofCxOkH (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    {Dt : State → Prop} (J : InvS) {T : Expr → Prop} {L : Lbl} {ls : Lsize} {l : WeakMem.AllocLabel} {b n : Nat}
    (hL : Reach (Ar) (fun _ => none) (fun _ => 0) L ls) (hl : L l = none)
    (hAL : Spike.Lib.HeapLand.AllocLand (Ar).heap (Ar).cells b n) {j : Nat} {d : Decl}
    (hd : (compiled2 p)[j]? = some d) (hT : d.name = "rodata" → ∀ x cn τ e, ¬ T (.let_ x (.newBuf cn τ) e))
    {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64}
    {G0 : Ctl → Prop} {Ab' : FragS isa} (hc : CxOkH h hp j R F fs fp ra tp G0 Ab') :
    (CXT J Dt (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n) hd T) (rbR R) F fs fp ra tp G0
      Ab' := by
  obtain ⟨d', hd', L1, D1, fS, nS, v, g, fr, J', hn, hfS, hnS, hL0, hLm, hL8, hD18, hL1, hrow,
    ⟨hR0, hR8, hF, hFF, -, -, hct, -⟩, hwn, -, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hc
  obtain rfl : d' = d := Option.some.inj (hd'.symm.trans hd)
  have hT' := hT hn
  exact cxLB_updT h hp J hL hl hAL hd
    (setupCxLB_ofPreT (T := T) h hp hty J v hfS hnS hL0 hLm hL8 hD18 hL1 hrow hd hn hR0 hR8 hF
      (fun m hm => ⟨⟨(hFF m hm).1.1.2, (hFF m hm).1.2⟩, (hFF m hm).2⟩) hct hwn (allocW2At_noNb hT')
      fun _ _ _ _ hJ hJT hA => (nbAb_noNb hT' hJ hJT hA).elim)
    (allocW2At_noNb hT') fun _ _ _ _ hJ hJT hA => (nbAb_noNb hT' hJ hJT hA).elim

/-- **A landings' context's `ResumeCx2T` at an extended placement on a walk
restriction with no allocation** (`H1RestXWT.hresL`'s field at `CxOk :=
CxOkH h hp`): at a restriction `Tr` whose points of `rodata`'s walk hold no
allocation's `let` (`hT`), the context's `CxLB` at `TailAt2 p j ∧ Tr j`
(`cxLBT_ofCxOkH`), its `ResumeCx2T` by `resumeCx2T_ofCxLB_noCall`: the
entry region's facts from `CxOkH`'s setup call's premises, the body's blocks
by `cxBlk2_ofFn` at the extended `CxLB` (the return address `scc_rt_main`'s
marshalling block, off the write abort; the jump targets by `tgOkB`), the
abort node empty at an addition-free body (`hno`). -/
theorem resumeCx2T_ofCxOkH (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    {Dt : State → Prop} (J : InvS) (hA : Spike.Lib.X64.Alloc.allocIn OP = true) (hTg : tgOkB OP = true)
    (hnc : ∀ (j : Nat) (d : Decl), (compiled2 p)[j]? = some d → d.name = "rodata" →
      (tailsL d.body).all (fun t => !isCallLet t) = true)
    (hTn : ∀ (j : Nat) (d : Decl), (compiled2 p)[j]? = some d → d.name = "rodata" →
      ∀ x cn τ e, TailAt2 p j (.let_ x (.newBuf cn τ) e) → Scc.Lower.elem2 τ = true)
    (hno : ∀ (j : Nat) (d : Decl), (compiled2 p)[j]? = some d → d.name = "rodata" → addFreeT d.body = true)
    {Tr : Nat → Expr → Prop}
    (hT : ∀ (j : Nat) (d : Decl), (compiled2 p)[j]? = some d → d.name = "rodata" →
      ∀ x cn τ e, ¬ (TailAt2 p j (.let_ x (.newBuf cn τ) e) ∧ Tr j (.let_ x (.newBuf cn τ) e))) :
    ∀ L ls l b n, Reach (Ar) (fun _ => none) (fun _ => 0) L ls → L l = none →
      Spike.Lib.HeapLand.AllocLand (Ar).heap (Ar).cells b n →
    ∀ j d (hd : (compiled2 p)[j]? = some d) R F fs fp ra tp G0 Ab, CxOkH h hp j R F fs fp ra tp G0 Ab →
      Spike.Lib.X64.PhRec.ph LY0 (Int64.ofBitVec ra).toBitVec.toNat =
        Spike.Lib.X64.PhRec.ph LY0 ((LY0).lab raL).toBitVec.toNat →
      ResumeCx2T (W2R J Dt (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n)) (KT) p
        (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n)
        (MSR J (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n))
        (fnCode2OfPMe hp h Λ j d hd) R F fs fp ra tp G0 Ab (Tr j) := by
  intro L ls l b n hL hl hAL j d hd R F fs fp ra tp G0 Ab hc hra
  have H := cxLBT_ofCxOkH h hp hty J (Dt := Dt) (T := fun t => TailAt2 p j t ∧ Tr j t) hL hl hAL hd
    (hT j d hd) hc
  obtain ⟨d', hd', L1, D1, fS, nS, v, g, fr, J', hn, hfS, hnS, hL0, hLm, hL8, hD18, hL1, hrow,
    ⟨hR0, hR8, hF, hFF, hraE, htp, hct, hbase⟩, hwn, hSB, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hc
  have e : d = d' := Option.some.inj (hd.symm.trans hd')
  subst e
  obtain ⟨w, -, -, hmem, hcx⟩ := fnCode2OfPMe_spec2 hp h Λ j d hd
  have hframe : (fnCode2OfPMe hp h Λ j d hd).fr.size = fS := by
    rw [hcx]; exact hrow _ hmem rfl (by show Scc.Lower.Names.user d.name = _; rw [hn])
  have hpN := Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hp
  have hs' : (Scc.Lower.setupOf p).isSome = true := by rw [hty]; rfl
  -- the setup call's return point (`scc_rt_main`'s marshalling block at `sp0`) is off the write abort
  have hraP : PosOff OP (Ly).lab (Int64.ofBitVec g.ra) := by
    have hin := Spike.Lib.X64.Rt.mainSIn_of_okS (rtCodeOkS_setupWords2 h hp hs')
    simp only [Spike.Lib.X64.Rt.mainSIn, Bool.and_eq_true] at hin
    have h0 := posOff_of_blockAtB (lab := (Ly).lab) hin.1.1.2 (by simp only [setupMC]; decide)
      (by simp [Spike.Lib.X64.Rt.marshal] <;> omega)
    rw [Spike.Lib.X64.Flow.ofNat_zero'] at h0
    rwa [hraE, Int64.ofBitVec_toBitVec]
  haveI := (LY0).valid
  have hI := Spike.Lib.X64.PhRec.instOk_ofPlaceOK h (Scc.Lower.imms2Of p) (rS := rS0 (Ly))
  have hblk := cxBlk2_ofFn (Λ := (Ly).Λ) hI (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h) hpN
    (fnCode2OfPMe hp h Λ j d hd) H.hFS H.hR H.hR8 H.hloF (by have := H.hhi; omega) H.hl H.hh
    (Spike.Lib.X64.Rt.rS0_sub _) (Spike.Lib.X64.Rt.fitS_of_sub _ (Spike.Lib.X64.Rt.rS0_sub _)) H.hFO H.hfp
    H.hG0F (fun _ _ h => h) hraP (hTg_of_tgOkB hTg (fun _ _ h => h) (Ly).lab)
    (rd := Spike.Lib.LowerNode.IsNum) (G := G2 h p) (μ := Mk) (own := Spike.Lib.X64.PhRec.own (Ly))
    (Tk := Spike.Lib.X64.PhRec.Tk (Ly)) (ar := Ar) (J := IN (Ar) (fun _ => none) (fun _ => 0) J) (Dt := Dt)
    (fp := g.fp) (lsize := Spike.Lib.AllocReach.updN ls l n)
  refine resumeCx2T_ofCxLB_noCall (Λ := (Ly).Λ) hI (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h)
    hA (Spike.Lib.X64.Rt.rS0_sub _)
    (Spike.Lib.X64.Rt.fitS_of_sub _ (Spike.Lib.X64.Rt.rS0_sub _)) hpN (fnCode2OfPMe hp h Λ j d hd) (Tr := Tr j)
    (fun t ht => ht d hd) (hnc j d hd hn) (hTn j d hd hn) hra hF hR0
    (by show -D1 ≤ _; rw [hframe]; omega) (by show (8 : Int) ≤ 8; exact Int.le_refl _) ?_ H ?_
    (fun c0 hc0 pc t s lits cs bufs blk hsub hk => hblk.1 c0 hc0 pc t s lits cs bufs blk hsub hk nofun)
    (fun c0 hc0 pc t s lits cs bufs k blk hsub hk h1 =>
      hblk.2 c0 hc0 pc t s lits cs bufs k blk hsub hk h1 nofun)
    (fun _ _ s c' hA' => by
      exfalso
      obtain ⟨-, -, -, -, σ, -, -, ⟨⟨sv, lits, hAb, -, -, -, hT'⟩, -⟩, -⟩ := hA'
      obtain ⟨x, a, b', e, -, -, -, -, -, -, he, -⟩ := hAb.1
      exact tailOf_addFree (hT'.1 d hd) (hno j d hd hn) x a b' e he)
  · intro pc zc g k hb
    rw [(fnCode2OfPMe_spec hp h Λ j d hd).2.1] at hb
    exact cdOf_blC hI.lays hI.endOk pc zc g k (by rw [hI.labOk]; exact hb.1.1)
  · rw [(fnCode2OfPMe_spec hp h Λ j d hd).1]

end Assembled

section Hello1

open Spike.Lib.LowerNode (hello1o_accepted2)

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
  {sizes : List Nat} {labelOffs : List (String × Nat)}
  (h : placeOKAt pcfg (lay2 Λ Spike.Test.Hello1MainSrc.hello1o)
    (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg Spike.Test.Hello1MainSrc.hello1o) sizes labelOffs) = true)

set_option linter.unusedVariables false in
/-- **`cxLBT_ofCxOkH` at `hello1o`**, at `rodata`'s walk restricted to the
points after its only allocation (`TrNb`; no allocation there:
`hello1_rodata_trNoNbT`). -/
theorem hello1_cxLBT {ty : Ty} (hty : Scc.Lower.setupOf Spike.Test.Hello1MainSrc.hello1o = some ty)
    {Dt : State → Prop} (J : InvS) {L : Lbl} {ls : Lsize} {l : WeakMem.AllocLabel} {b n : Nat}
    (hL : Reach (Spike.Lib.X64.Rt.arOf (lay2 Λ Spike.Test.Hello1MainSrc.hello1o)) (fun _ => none) (fun _ => 0) L ls)
    (hl : L l = none)
    (hAL : Spike.Lib.HeapLand.AllocLand (Spike.Lib.X64.Rt.arOf (lay2 Λ Spike.Test.Hello1MainSrc.hello1o)).heap
      (Spike.Lib.X64.Rt.arOf (lay2 Λ Spike.Test.Hello1MainSrc.hello1o)).cells b n) {j : Nat} {d : Decl}
    (hd : (compiled2 Spike.Test.Hello1MainSrc.hello1o)[j]? = some d)
    {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64}
    {G0 : Ctl → Prop} {Ab' : FragS isa} (hc : CxOkH h hello1o_accepted2 j R F fs fp ra tp G0 Ab') :
    let p := Spike.Test.Hello1MainSrc.hello1o
    let hp := hello1o_accepted2
    (CXT J Dt (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n) hd
      (fun t => TailAt2 p j t ∧ TrNb (TailAt2 p j) t)) (rbR R) F fs fp ra tp G0 Ab' :=
  cxLBT_ofCxOkH h hello1o_accepted2 hty J (T := fun t => TailAt2 Spike.Test.Hello1MainSrc.hello1o j t ∧
    TrNb (TailAt2 Spike.Test.Hello1MainSrc.hello1o j) t) hL hl hAL hd (hello1_rodata_trNoNbT hd) hc

end Hello1

section Hello1R

open Spike.Lib.LowerNode (hello1o_accepted2)
open Spike.Lib.X64.Rt (rtF)

/-- The program. -/
local notation "P1" => Spike.Test.Hello1MainSrc.hello1o

variable {Λx : Scc.Sem.Layout}

set_option hygiene false in
/-- The layout: any layout at which the placement check passes (`h`). -/
local notation "Le" => Λx

/-- The compiler's output for the program at the certificate's sizes and label offsets. -/
local notation "OX" =>
  Out.ofEmitted (Scc.Lower.X64.lowerAll SccCertificate.config P1) SccCertificate.sizes SccCertificate.labelOffs

variable (h : placeOKAt SccCertificate.placeCfg (lay2 Le P1) OX = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "LyH" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (Spike.Lib.LowerNode.imms2Me Le P1)

set_option hygiene false in
/-- The allocator's arena of the output. -/
local notation "ArH" => Spike.Lib.X64.Rt.arOf (lay2 Le P1)

set_option hygiene false in
/-- **`W2` at the record** at a placement `L`, `ls`, over `IN … J` (`H1RestXWT`'s at `Dt := fun _ => True`). -/
local notation "W2H" J:max L:max ls:max =>
  fun s c fs => W2 (lay2 Le P1) (Spike.Lib.X64.PhRec.μ (LyH)) P1 Spike.Lib.LowerNode.IsNum (G2 h P1)
    (Spike.Lib.X64.PhRec.own (LyH)) (Spike.Lib.X64.Rt.rS0 (LyH)) (Spike.Lib.X64.PhRec.Tk (LyH)) (ArH)
    (IN (ArH) (fun _ => none) (fun _ => 0) J) (fun _ => True) (Spike.Lib.X64.WriteAb.Ab (LyH).lab) L ls s c fs

set_option hygiene false in
/-- The extended placement's labels. -/
local notation "LU" => Spike.Lib.AllocReach.upd L l b

set_option hygiene false in
/-- The extended placement's sizes. -/
local notation "LN" => Spike.Lib.AllocReach.updN ls l n

set_option hygiene false in
/-- The start's frame condition: the runtime's words unloaded and no heap or image word loaded. -/
local notation "WNF" => fun m => Spike.Lib.DmemPriv.WordsNone (LyH).Λ (MachineData.dmem m) ∧ rtF (LyH) m

set_option hygiene false in
/-- `hello1o`'s landings at the bottom keys `BotHR`. -/
local notation "ElR" => ElX h (fnCode2OfPMe hello1o_accepted2 h Le) (CxOkH h hello1o_accepted2) (BotHR h)

/-- **`hello1`'s `H1RestXWT` at the walk past `rodata`'s allocation**
(`hello1_final'`'s `HR` at `Tr := fun j => TrNb (TailAt2 P1 j)`), from the
bottom keys' exits `hW` alone (`hello1_hbot`'s): `hAW` by `hAW_H1RestXW`;
`hTr` by `TrNb.intro`; `hresL` by `resumeCx2T_ofCxOkH` (no allocation on
the restricted walk: `hello1_rodata_trNoNbT`; no call, element types,
addition-free: `hello1_rodata_noCall`, `hello1_hTn`, `hello1_rodata_addFree`;
the allocator's code and jump targets: `hello1_allocIn`, `hello1_tgOkB`);
`hresS` vacuous (no call in `rodata`: `hello1_rodata_noCallT`); `hbot` by
`hello1_hbot`. -/
theorem hello1_restXT {E : Entry}
    (hW : ∀ J : InvS, (∀ L ls, Reach (ArH) (fun _ => none) (fun _ => 0) L ls →
        ∀ s c fs, StartsSX h E (WNF) (ElR) (fun _ => True) (ab2 P1 (LyH).lab) L ls s c fs → J L ls s c fs) →
      ∀ L ls l b n, Reach (ArH) (fun _ => none) (fun _ => 0) L ls → L l = none →
        Spike.Lib.HeapLand.AllocLand (ArH).heap (ArH).cells b n →
      ∀ k fs, BotHR h k fs → ∀ c0 ty, k.G0 c0 → (∃ d, (compiled2 P1)[k.j]? = some d ∧ d.retTy = ty) →
        ∀ s c, ExitC2SL P1 (LU) (LyH).exe (LyH).endPc (rbR k.R) k.F k.fp k.ra k.tp c0 fs ty
          (fun _ _ _ => False) s c fs → (W2H J (LU) (LN)) s c fs) :
    H1RestXWT h E (fnCode2OfPMe hello1o_accepted2 h Le) (CxOkH h hello1o_accepted2) (BotH h) (fun _ => True)
      (fun j => TrNb (TailAt2 P1 j)) where
  hAW := hAW_H1RestXW h hello1o_accepted2 hello1_hty.choose_spec hello1_hTn
  hTr := fun _ _ _ _ _ _ _ _ hT ht => TrNb.intro hT ht
  hresL := fun J _ => resumeCx2T_ofCxOkH h hello1o_accepted2 hello1_hty.choose_spec J (hello1_allocIn h)
    hello1_tgOkB hello1_rodata_noCall (fun j d hd _ => hello1_hTn j d hd) hello1_rodata_addFree
    (fun _ _ hd hn => hello1_rodata_trNoNbT hd hn)
  hresS := fun _ _ _ _ _ _ _ _ _ _ j d hd _ _ _ _ _ _ _ _ hc _ ⟨x, g, b, e, hT⟩ => by
    exfalso
    obtain ⟨d', hd', -, -, -, -, -, -, -, -, hn, -⟩ := hc
    obtain rfl : d' = d := Option.some.inj (hd'.symm.trans hd)
    exact hello1_rodata_noCallT hd hn x g [] b [] e hT
  hbot := hello1_hbot h hW

omit h in
/-- **`hello1_final'` with `HR` by `hello1_restXT`**: `hello1`'s x86-64
statement from the bottom keys' exits `hW` and the allocator's `W2`
instance at the setup frame `OpenAWF`. -/
theorem hello1_finalT
    (h0 : placeOKAt SccCertificate.placeCfg Le
      (Out.ofEmitted (Scc.Lower.X64.lowerAll SccCertificate.config Spike.Test.Hello1MainSrc.hello1o)
        SccCertificate.sizes SccCertificate.labelOffs) = true)
    (hW : ∀ E : Entry, E.Ok (lay2 Le P1) → ∀ h : placeOKAt SccCertificate.placeCfg (lay2 Le P1) OX = true,
      ∀ J : InvS, (∀ L ls, Reach (ArH) (fun _ => none) (fun _ => 0) L ls →
        ∀ s c fs, StartsSX h E (WNF) (ElR) (fun _ => True) (ab2 P1 (LyH).lab) L ls s c fs → J L ls s c fs) →
      ∀ L ls l b n, Reach (ArH) (fun _ => none) (fun _ => 0) L ls → L l = none →
        Spike.Lib.HeapLand.AllocLand (ArH).heap (ArH).cells b n →
      ∀ k fs, BotHR h k fs → ∀ c0 ty, k.G0 c0 → (∃ d, (compiled2 P1)[k.j]? = some d ∧ d.retTy = ty) →
        ∀ s c, ExitC2SL P1 (LU) (LyH).exe (LyH).endPc (rbR k.R) k.F k.fp k.ra k.tp c0 fs ty
          (fun _ _ _ => False) s c fs → (W2H J (LU) (LN)) s c fs)
    (HA : ∀ E : Entry, E.Ok (lay2 Le P1) → ∀ h : placeOKAt SccCertificate.placeCfg (lay2 Le P1) OX = true,
      OpenAWF h hello1o_accepted2 E (ElH h) (fun _ => True))
    (hpa : Scc.Cert.Link.X64.parsesTo ⟨SccCertificate.asm, SccCertificate.sizes, SccCertificate.labelOffs⟩
      SccCertificate.outLit.prog SccCertificate.outLit.secs = true)
    {B : Scc.Sem.Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells) {arch : WeakMem.Arch} :
    CorrectE 1 (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch P1) P1) (lay2 Le P1) B
      ⟨SccCertificate.asm, SccCertificate.sizes, SccCertificate.labelOffs⟩ :=
  hello1_final'_gen h0 (fun E hE h => hello1_restXT h (hW E hE h)) HA hpa hB

/-- **`hello1`'s `H1RestXWT` closed** at `TrNb (TailAt2 P1 j)`:
`hello1_restXT` at the bottom keys' exits `hello1_hWBot`. -/
theorem hello1_restXTW {E : Entry} :
    H1RestXWT h E (fnCode2OfPMe hello1o_accepted2 h Le) (CxOkH h hello1o_accepted2) (BotH h) (fun _ => True)
      (fun j => TrNb (TailAt2 P1 j)) :=
  hello1_restXT h (hello1_hWBot h)

omit h in
/-- **`hello1`'s x86-64 statement from `OpenAWF` alone**: `hello1_finalT`
at the bottom keys' exits `hello1_hWBot`. -/
theorem hello1_finalTW
    (h0 : placeOKAt SccCertificate.placeCfg Le
      (Out.ofEmitted (Scc.Lower.X64.lowerAll SccCertificate.config Spike.Test.Hello1MainSrc.hello1o)
        SccCertificate.sizes SccCertificate.labelOffs) = true)
    (HA : ∀ E : Entry, E.Ok (lay2 Le P1) → ∀ h : placeOKAt SccCertificate.placeCfg (lay2 Le P1) OX = true,
      OpenAWF h hello1o_accepted2 E (ElH h) (fun _ => True))
    (hpa : Scc.Cert.Link.X64.parsesTo ⟨SccCertificate.asm, SccCertificate.sizes, SccCertificate.labelOffs⟩
      SccCertificate.outLit.prog SccCertificate.outLit.secs = true)
    {B : Scc.Sem.Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells) {arch : WeakMem.Arch} :
    CorrectE 1 (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch P1) P1) (lay2 Le P1) B
      ⟨SccCertificate.asm, SccCertificate.sizes, SccCertificate.labelOffs⟩ :=
  hello1_finalT h0 (fun _ _ h => hello1_hWBot h) HA hpa hB

end Hello1R

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.cxLBT_ofCxOkH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cxLBT_ofCxOkH

/-- info: 'Spike.Lib.LowerX64.hello1_cxLBT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hello1_cxLBT

/-- info: 'Spike.Lib.LowerX64.resumeCx2T_ofCxOkH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms resumeCx2T_ofCxOkH

/-- info: 'Spike.Lib.LowerX64.hello1_restXT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hello1_restXT

/-- info: 'Spike.Lib.LowerX64.hello1_finalT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hello1_finalT

/-- info: 'Spike.Lib.LowerX64.hello1_restXTW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hello1_restXTW

/-- info: 'Spike.Lib.LowerX64.hello1_finalTW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hello1_finalTW

end Spike.Lib.LowerX64
