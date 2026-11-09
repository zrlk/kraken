/-
**hello's root, level 0, at `ownGHXW`** (x86-64 only; the `ownGHXW` instance of `X64HelloRootUL`'s live part,
`wc_rodata`'s counter add's tail and the level-0 `hW0`, AArch64's `A64HelloLandRU.hW0_RdU`): the root's level 0
with main owning both TCB self words (`OX := ownGHXW Ly ntA`), at the context
`CXU := RootUL.CtxU (LandRU.CtxRdHg … OX)`, the child's stack unmapped.

The context keeps `U r1Of`, as `LandRU.CtxRdU` does at `ownGH`: the counter row (`RootUL.ctrRow_ofFTU`) lands at the
allocator's `c2`, and that landing is in level 1's statement (`StartH0H1.RdLandHg`) only with `r1Of` unmapped;
`inv0Hg` does not carry it, the context does.

- `takeU_Hg`, `inv0_upHg`, `hst0_UHg`: the lifts to `RootUL.CtxU` (AArch64 `A64HelloRootUL.takeU_H`, `inv0_upH`,
  `hst0_UH`) at an own map `own` (`W0Hg own`, `inv0Hg own`, `msBotHg own`); `W0`'s take and `U r1Of` do not read
  the own map.
- `HLandRdUg`: `wc_rodata`'s counter add's tail (AArch64 `A64HelloLandRd.HLandRdU`) at the reference side
  `LandRU.refHg own`.
- `hlandRd_UX`: `HLandRdUg OX` at `inv0Hg … OX`, given `wc_rodata`'s `hrd` at
  `msUHg OX`, level 1's `h1` at `RdLandHg OX` and `hhabctlRd` at `msBotHg OX`; the heap abort closed by
  `RdHAbX.hello_rd_hab_closedX` (so `hA13`).
- `hlandRd_rootX`: `hlandRd_UX` at `Ctx := CtxRdHg … OX`, `hrd` by `HrdRootX.hrd_RdHX`.
- `hW0_RdUX`: `hW0` at `helloDRg … OX` with `Ctx := CXU`, given `HLandRdUg OX` at `inv0Hg … CX …`.
- `hW0_rootX`: `hW0_RdUX` with `hlandRd_rootX`.
- `hst0_rootX`: `RootH0.hstHg`'s `hst0` at `OX` and `CXU`: `StartH0XR.hst0_XRc` at `rd := True`, `ls0 := ls`, its
  `hWe` by `WeRootX.hWe_rootX`, `hq` by `Hq0.hq0_H`, `hctr2` by `X64HelloCtr2.hctr2_H`, lifted by `hst0_UHg`.

## Differences from the AArch64 version

AArch64 has no counterpart: main owns no TCB word there, so its root's level 0 is at `ownGH` only
(`A64HelloCtxRdU`). Against x86-64 at `ownGH` (`LandRU.CtxRdU`): the memory sides own `ownGHXW`, the start's
level is `StartWcS.WSg OX`, the heap abort's closure `hello_rd_hab_closedX` (which asks `hA13`), and `hrd` is
`hrd_RdHX` (no `hctx`).
-/
import Spike.Lib.X64HelloLandRU
import Spike.Lib.X64HelloStartH0XR
import Spike.Lib.X64HelloWeRootX
import Spike.Lib.X64HelloHq0
import Spike.Lib.X64HelloCtr2
import Spike.Lib.X64HelloRdHAbCX

namespace Spike.Lib.X64.HelloPh.RootL0X

variable {asm : Scc.Sem.X64.Asm}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Entry)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64ConsumerA (SegInvS TakeCKS I3 SFactsACH)
open Spike.Lib.X64.WakeWf (DtW)
open Spike.Lib.X64.HelloPh (lo)
open Spike.Lib.X64.HelloPh.StartGlue (X0WH)
open Spike.Lib.X64.HelloPh.StartWcS (WSg rdJH)
open Spike.Lib.X64 (At enter)
open Spike.Lib.X64.Flow.Ret0 (CallerCells tpOf)
open Spike.Lib.X64.WakePh.MainGlue (FS JS RS tcbS topS)
open Spike.Lib.X64.Flow.Hello1 (AG mR mF mRdJ0 aR)
open Spike.Lib.X64.Flow.HelloRd (rN rX rXF RdPreW RdCtx)
open Spike.Lib.X64.KeepUn (U unXa)
open Spike.Lib.X64.KeepTP (TP tpXa)
open Spike.Lib.X64.HelloPh.StartH0H1 (RdLandHg)
open Spike.Lib.X64.Alloc (Call N Ea)
open Spike.Lib.X64.HelloPh.StartH0G (helloLsw)
open Spike.Lib.X64.HelloPh.StartH0B (StartPH W0Hg)
open Spike.Lib.X64.HelloPh.StartH0U (msUHg)
open Spike.Lib.X64.HelloPh.RootH0 (msBotHg inv0Hg)
open Spike.Lib.X64.HelloPh.Land (CtrOkS CtrAtF GcRdH)
open Spike.Lib.X64.HelloPh.LandRU (refHg CtxRdHg)
open Spike.Lib.X64.HelloPh.RootUL (CtxU)
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib (FragS Frag SegWS MemSide PlaceWX Region)
open Spike.Lib.X64WakeLoadT (L0T ls0T)
open Spike.Lib.X64.WakeH1Inv (segInvS_weakW)
open Spike.Lib.X64.WakePh.RootUL (w0_mono)
open Spike.Lib.X64.HelloPh.C0S (c0S)
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.X64HelloRootO (helloDRg)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.X64.AS

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The root's immediate table at the certificate's table `i0` (as `StartH0U`). -/
local notation "IH" => Spike.Lib.X64.HelloImms.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw IH

set_option hygiene false in
local notation "AR" => Spike.Lib.X64.WakeOD.arW hpw IH

set_option hygiene false in
local notation "NT" => Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab

set_option hygiene false in
/-- main's owned words before the spawn, both TCB self words included. -/
local notation "OX" => Spike.Lib.X64.HelloPh.ownGHXW (Ly) NT

set_option hygiene false in
local notation "RS0" => Spike.Lib.X64.Rt.rS0 (Ly)

set_option hygiene false in
local notation "R1" => Spike.Lib.X64.Rt.PreChild.r1Of (Ly).lab

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

set_option hygiene false in
/-- The allocator's labels. -/
local notation "LBL" => (_root_.Executable.labels (Ly).exe).label

set_option hygiene false in
local notation "AX" => (Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL

set_option hygiene false in
local notation "FR" => Spike.Lib.X64HelloRdCf.frH c0S.env

set_option hygiene false in
local notation "KR" => Spike.Lib.X64.PhRec.K (Ly) (RS0)

set_option hygiene false in
/-- `wc_rodata`'s caller's entry invariant at the root, at `scc_rt_main`'s region `RS helloLsw v`. -/
local notation "J'" => fun v : BitVec 64 => rdJH (Ly).lab (RS helloLsw v) (JS (Ly) 0#64 c0S)

set_option hygiene false in
/-- The first stack's top. -/
local notation "TOP" => topS (Ly) 0#64

set_option hygiene false in
/-- main's thread pointer. -/
local notation "TV" => tpOf (tcbS (Ly))

set_option hygiene false in
/-- `wc_rodata`'s frame condition at the first stack's top. -/
local notation "FT" => mF (RS helloLsw (TOP)) (FS (Ly) (RS0) helloLsw 0#64 (TOP))

set_option hygiene false in
/-- `wc_rodata`'s region at the first stack's top. -/
local notation "MT" => mR (RS helloLsw (TOP))

set_option hygiene false in
local notation "μE" => (Scc.Sem.X64.target (Scc.Sem.X64.kernel 2) E).marks asm (Ly).Λ

/-! ## `RootUL` at an own map -/

section Own

variable (own : State → List (Loc × Val))

/-- **`W0Hg own`'s outside moves keep `r1Of` unmapped** (AArch64 `RootUL.takeU_H` at `own`). -/
theorem takeU_Hg (E : Entry) (Dt : State → Prop) (Cx : FragS isa) (lsize : Lsize) (frM : TermRun.Frame) :
    ∀ s c fs, W0Hg (asm := asm) hpw IH own E Dt Cx lsize frM s c fs → ∀ s',
      TakeCKS (AX) (Spike.Lib.X64.HelloPh.ClH (Ly)) s s' → U (R1) s → U (R1) s' := by
  have hbd' : (Spike.Lib.X64.Flow.Ret0.stacksA (Ly).lab).toNat + 32768 < 2 ^ 64 :=
    Spike.Lib.X64WakeHClC.hbd_W hpw IH
  obtain ⟨h1l, h1s⟩ := Spike.Lib.X64.Rt.Ti2.r1Of_eq hbd'
  rw [(Ly).lab_stacks] at h1l hbd'
  have hSl : (RS0).lo = (Ly).stacksA.toNat := by
    show ((Ly).stacksA + 0#64).toNat = _; rw [BitVec.add_zero]
  have hSs : (RS0).size = 16384 := rfl
  have hw1 : (R1).lo + (R1).size ≤ 2 ^ 64 := by omega
  have hwS : (RS0).lo + (RS0).size ≤ 2 ^ 64 := by omega
  have hd : (R1).Disjoint (RS0) := by unfold Scc.Sem.Range.Disjoint; omega
  intro s c fs hW s' hk hu
  obtain ⟨-, pm, rfl⟩ := (Spike.Lib.X64.HelloPh.StartH0B.takeCKS_iffH hpw IH hW.2.1).1 hk
  exact Spike.Lib.X64.KeepUn.take_un pm hd hw1 hwS hu

variable (E : Entry) (rd : TermRun.Word → Prop) (Ctx : FragS isa) (ls : Lsize) (frM : TermRun.Frame)
  (inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa)
  (inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa)

set_option hygiene false in
local notation "I0" => fun Cx => inv0Hg (asm := asm) hpw IH E rd Cx ls ls frM inv1 inv2 own

/-- **`inv0Hg own` at `Ctx` with `r1Of` unmapped is at `CtxU Ctx`** (AArch64 `RootUL.inv0_upH` at `own`). -/
theorem inv0_upHg : ∀ s c fs, (I0) Ctx s c fs → U (R1) s → (I0) (CtxU hpw i0 Ctx) s c fs :=
  fun s c fs hi hu => Spike.Lib.X64GfpS.le_gfpS (segInvS_weakW
    (Spike.Lib.X64.WakePh.RootUL.SegInvS.keepUn (fun _ => rfl) Spike.Lib.X64GfpS.segInvS_gfpS
      (takeU_Hg hpw i0 own E _ _ _ _)) fun _ _ _ h => w0_mono h.1 fun hc => ⟨hc, h.2⟩) s c fs ⟨hi, hu⟩

/-- **`hst0` at `CtxU Ctx` from `hst0` at `Ctx`, at `own`** (AArch64 `RootUL.hst0_UH` at `own`). -/
theorem hst0_UHg (hE : E.Ok (Ly).Λ) (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    (hst0 : SegWS (W0Hg (asm := asm) hpw IH own E DtW Ctx (ls0T ls) frM)
      (TakeCKS (AX) (Spike.Lib.X64.HelloPh.ClH (Ly))) helloSrc (LB)
      (msBotHg (asm := asm) hpw IH E rd ls inv1 inv2 own) (StartPH hpw IH E) (fun _ _ _ => False)) :
    SegWS (W0Hg (asm := asm) hpw IH own E DtW (CtxU hpw i0 Ctx) (ls0T ls) frM)
      (TakeCKS (AX) (Spike.Lib.X64.HelloPh.ClH (Ly))) helloSrc (LB)
      (msBotHg (asm := asm) hpw IH E rd ls inv1 inv2 own) (StartPH hpw IH E) (fun _ _ _ => False) := by
  obtain ⟨inv, hP, hS⟩ := Spike.Lib.X64ConsumerA.SegInvS.ofSegWS hst0
  have hS' := segInvS_weakW (Spike.Lib.X64.WakePh.RootUL.SegInvS.keepUn (fun _ => rfl) hS
      (takeU_Hg hpw i0 own E _ _ _ _))
    (W := W0Hg (asm := asm) hpw IH own E DtW (CtxU hpw i0 Ctx) (ls0T ls) frM)
    fun _ _ _ h => w0_mono h.1 fun hc => ⟨hc, h.2⟩
  refine ⟨fun s c fs => inv s c fs ∧ U (R1) s, fun s c fs hp => ⟨hP s c fs hp, ?_⟩,
    fun s c fs hi => (hS' s c fs hi).1,
    fun s c fs hi => ⟨fun hk => ((hS' s c fs hi).2.1 hk).mono fun _ _ _ h => h.mono fun _ _ _ => .inl,
      (hS' s c fs hi).2.2.mono fun _ _ _ => .inl⟩⟩
  obtain ⟨rfl, -, -⟩ := hp
  exact Spike.Lib.X64.WakePh.StartH0X.entry_U (hpw := hpw) (i := IH) hE.1 hA13 _ _

end Own

/-! ## The counter add's landing at `OX` -/

variable (E : Entry) (rd : TermRun.Word → Prop) (ls : Lsize)

/-- **`wc_rodata`'s counter add's tail at an own map `own`** (AArch64 `A64HelloLandRd.HLandRdU`): from the
allocator's `c2` after a counter add of `wc_rodata`'s buffer call at a memory side `ms0` that is `refHg own fs`
but for `xa`, with `U r1Of` and `TP`, the state is in `Q` at the frames `fs`. -/
def HLandRdUg (own : State → List (Loc × Val)) (Q : FragS isa) : Prop :=
  ∀ fs (ms0 : MemSide isa) R F q, ms0 = { refHg (asm := asm) hpw i0 E rd ls own fs with xa := ms0.xa } →
    GcRdH hpw i0 fs ms0 R F q → CtrOkS ms0 LBL R F q →
    ∀ s c, At (Ly).exe (Ly).endPc R F (N LBL ms0 q .c2) s c → U (R1) s → TP (TV) s → Q s c fs

variable (Ctx : FragS isa) (ls0 : Lsize) (inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa)
  (inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa)

set_option hygiene false in
/-- `msBotHg`'s fragment: `I3` with its `inv0` disjunct `⊥`. -/
local notation "IB" => I3 (AR) (LB) (ls0T ls) (fun _ _ _ => False) inv1 inv2

set_option hygiene false in
/-- The root's start-form memory sides at `IB`, owning `OX`. -/
local notation "MSU" => msUHg (asm := asm) hpw i0 (OX) E rd (IB) ls

set_option hygiene false in
local notation "MSB" => msBotHg (asm := asm) hpw IH E rd ls inv1 inv2 (OX)

set_option hygiene false in
/-- The start's level at the root's choices, at `OX`. -/
local notation "WP" => WSg (OX) (Ly) (AR) helloSrc DtW (Spike.Lib.X64.HelloPh.ClH (Ly)) Ctx (LB) (ls0T ls0) (FR)
  (X0WH (Ly) (AX))

set_option maxHeartbeats 1600000 in
/-- **`HLandRdUg OX` at the root's level-0 invariant `inv0Hg … OX`** (AArch64 `A64HelloLandRd.hlandRd_U`): the
allocator's rest from `c2` inside `NoSetFsW` at `tpXa (msUHg OX [FR])`, resumed at `rX .abort`, the thread pointer
kept, moved to `msBotHg OX` with `r1Of` unmapped, closed by `hello_rd_hab_closedX`. Premises: `wc_rodata`'s `hrd`
at `msUHg OX`, level 1's `h1` at `RdLandHg OX` and `hhabctlRd` at `msBotHg OX`. -/
theorem hlandRd_UX (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some SccCode.helloCells) (hlo0 : Λ0.code.lo = lo)
    (hc : Spike.Lib.X64.Rt.CtrZ o) (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    (hrd : ∀ v m0 σC, RdPreW (Spike.Lib.X64.WakeTP.tpG (TV) fun s c => WP s c [FR]) KR (Ly).exe (Ly).endPc
      (mR (RS helloLsw v)) (mF (RS helloLsw v) (FS (Ly) (RS0) helloLsw 0#64 v) m0 σC) ((MSU) [FR])
      (mRdJ0 ((J') v) σC) (mRdJ0 ((J') (TOP)) σC))
    {W1 : WeakMem.AllocLabel → Nat → Nat → FragS isa} {K : State → State → Prop}
    {ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isa}
    /- level 1's statement: rodata's landing at `OX` is in `inv1 … [FR]` -/
    (h1 : Spike.Lib.X64HelloPreA.H1StmtHF W1 K (AR) (LB) ms1 (Ly)
      (RdLandHg (asm := asm) hpw i0 (OX) E rd (IB) ls (fun σC => mRdJ0 ((J') (TOP)) σC)) inv1 [FR])
    (hhabctlRd : ∀ σC, Spike.Lib.X64.HelloPh.HabCtlRd.HabCtlRdH ((MSB) [FR]) (Ly).lab helloSrc (Ly).Λ (LB)
      (MT) (AR) [FR] (mRdJ0 ((J') (TOP)) σC)) :
    HLandRdUg (asm := asm) hpw i0 E rd ls (OX)
      (inv0Hg (asm := asm) hpw IH E rd Ctx ls0 ls (FR) inv1 inv2 (OX)) := by
  intro fs ms0 R F q hms hG _ s c hAt hU hT
  obtain ⟨X, rfl⟩ : ∃ X, ms0 = { refHg (asm := asm) hpw i0 E rd ls (OX) fs with xa := X } := ⟨_, hms⟩
  obtain ⟨rfl, hq, v, m0, σC, rfl, rfl, hra⟩ := hG
  -- the frame condition pins `v` at the first stack's top
  by_cases hv : v = TOP
  case neg =>
    obtain ⟨-, -, -, -, _, -, hF, -⟩ := hAt
    exact (hv hF.1.1.1.2.1.1).elim
  subst hv
  -- the layout's facts
  have hprog : (Ly).prog = SccCode.helloCells := Option.some.inj (hpa.symm.trans hhp)
  have hpL : Scc.Sem.X64.cellsOf asm = some (Ly).prog := by rw [hprog]; exact hhp
  obtain ⟨hpS, hendS, -⟩ := Spike.Lib.X64.HelloPh.LandR.hcode_H hpw i0 hpa hhp
  -- the ranges: `r1Of` disjoint from `rS0`, both in the address space
  have hbd' : (Spike.Lib.X64.Flow.Ret0.stacksA (Ly).lab).toNat + 32768 < 2 ^ 64 :=
    Spike.Lib.X64WakeHClC.hbd_W hpw IH
  obtain ⟨h1l, h1s⟩ := Spike.Lib.X64.Rt.Ti2.r1Of_eq hbd'
  rw [(Ly).lab_stacks] at h1l hbd'
  have hSl : (RS0).lo = (Ly).stacksA.toNat := by
    show ((Ly).stacksA + 0#64).toNat = _; rw [BitVec.add_zero]
  have hSs : (RS0).size = 16384 := rfl
  have hw1 : (R1).lo + (R1).size ≤ 2 ^ 64 := by omega
  have hwS : (RS0).lo + (RS0).size ≤ 2 ^ 64 := by omega
  have hd : (R1).Disjoint (RS0) := by unfold Scc.Sem.Range.Disjoint; omega
  -- the regions: `wc_rodata`'s at the call, the allocator's
  obtain ⟨-, hok0, hF0⟩ := Spike.Lib.X64.HelloPh.Land.fstable_FS hpw i0
  obtain ⟨hmR, hFm⟩ := Spike.Lib.X64.Flow.Hello1.mR_ok hok0 hF0
    (by show (8 - helloLsw : Int) ≤ -288; decide) (by show (8 : Int) ≤ 8; decide) m0 σC
  have haR : (aR (MT)).OK := Region.callee_ok hmR (by show (-208 : Int) ≤ -48 + -160; decide) (by decide)
    (by show (-48 : Int) < 8; decide) (by show (-48 : Int) + 8 ≤ 8; decide)
  -- the arena's facts at `msUHg OX` (`HrdArena.hmem_U`'s at `msUH`, `Call.OK` carried over field by field)
  have hcl : ((MSU) [FR]).cells = 4194304 := rfl
  have hqU : q.OK ((MSU) [FR]) (Ly).lab := { hq with }
  have hqT : q.OK (tpXa ((MSU) [FR]) (TV)) (Ly).lab := Spike.Lib.X64.Flow.Hello1.callOK_tp hqU
  have hmem := Spike.Lib.X64.HelloPh.HrdArena.hmem_U (asm := asm) hpw i0 (E := E) (rd := rd) (I := IB) (ls := ls)
    (fs := [FR]) hc (k0 := 0#64) (v := TOP)
  have hRdU := Spike.Lib.X64.HelloPh.StartH0H1.hRdU_of_h1Fg hpw i0 E h1
  -- the landing at `tpXa (msUHg OX [FR])`: one the arena hands out (`Ea` at `arOf`), the rest `h1`'s given
  -- `U r1Of` and the thread pointer
  have hxa : ∀ l b w s c, (LB) l = none →
      At (Ly).exe (Ly).endPc (aR (MT))
        (fun m => FT m0 σC m ∧ CallerCells (MT) (-48) (-160) 8 m ∧
          RdCtx (tpXa ((MSU) [FR]) (TV)) (Ly).lab (MT) (mRdJ0 ((J') (TOP)) σC) (mRdJ0 ((J') (TOP)) σC) q m)
        (Ea (tpXa ((MSU) [FR]) (TV)) q l b w) s c → (tpXa ((MSU) [FR]) (TV)).xa l b w s c := by
    intro l b w s c hl hA' ht
    replace hA' : At (Ly).exe (Ly).endPc (aR (MT)) _ (Ea ((MSU) [FR]) q l b w) s c := hA'
    have hAL : AllocLand (AR).heap (AR).cells b w := by
      obtain ⟨-, -, -, -, -, -, -, -, old, -, -, hb', hold, -, -, us, hus, hw⟩ := id hA'
      have hf : ((MSU) [FR]).off q.n q.τ = 8 := Spike.Lib.LowerX64.arOf_off_eq (Λ := (Ly).Λ) hqU.accs
      have hu : ((MSU) [FR]).units q.n q.τ = q.n * TermRun.nWords us + 1 :=
        Spike.Lib.LowerX64.arOf_units_fit (Ly).Λ q.n q.τ us hus (Nat.le_trans (Nat.le_add_left _ old) hold)
      show ((MSU) [FR]).heap + 8 ≤ b ∧ b + 8 * w ≤ ((MSU) [FR]).heap + 16 * ((MSU) [FR]).cells ∧
        w + 1 ≤ ((MSU) [FR]).cells
      rw [hf] at hb'; rw [hu, hcl] at hold; rw [hcl]; subst hw
      omega
    exact ⟨hAL, fun hU' => hRdU (TOP) m0 σC ⟨q, hqU⟩ _ (fun _ h => h.1)
      (fun _ ⟨_, _, h⟩ => h) l b w s c hl hA' hAL hU' ht⟩
  -- the allocator's rest from `c2` inside `NoSetFsW`, at `tpXa`, its only exit the heap abort
  have hAl := Spike.Lib.X64.Flow.seg_alloc_ofW_atNR (p := helloSrc) (lbl := LB) hpS hendS
    Spike.Lib.X64.Flow.HelloRd.hello_alloc
    (Spike.Lib.X64.HelloPh.Land.fstable_aRH (ms := tpXa ((MSU) [FR]) (TV)) (lab := (Ly).lab)
      (J0 := mRdJ0 ((J') (TOP)) σC) (J1 := mRdJ0 ((J') (TOP)) σC) (q := q) hmR hFm
      (by show (-208 : Int) ≤ -208; decide) (by show (8 : Int) ≤ 8; decide))
    haR (by simp [Region.callee]) (by simp [Region.callee]) hqT
    (fun a ha m hm => hmem q { hqU with } a ha m hm.1.1) hxa
    ((Spike.Lib.X64.Flow.HelloM.rdPreW_tpH (t := TV)
      (Spike.Lib.X64.Flow.HelloM.rdPreW_noMsrH hpS hendS (hrd (TOP) m0 σC))).alloc q hqT hra) .c2
  -- its exit resumed in `wc_rodata`'s frame
  have hres := Spike.Lib.X64.seg_resumeW (N := fun e : Empty => e.elim)
    (E := rXF (tpXa ((MSU) [FR]) (TV)) (Ly).lab (LB) (MT) (mRdJ0 ((J') (TOP)) σC))
    (F₂ := FT m0 σC) (M := fun _ => True)
    (PC := fun σC' => ∃ c, (rN (Ly).lab (MT) (mRdJ0 ((J') (TOP)) σC) (mRdJ0 ((J') (TOP)) σC) .call).J σC' c ∧
      (N (Ly).lab (tpXa ((MSU) [FR]) (TV)) q .e).J (enter (-48) σC') c)
    (Ex := fun _ : Unit => Spike.Lib.X64.Alloc.EX30 (Ly).lab (tpXa ((MSU) [FR]) (TV)) q (LB) .abort)
    (hAl.mono_post fun _ _ h => ⟨(), h, trivial⟩)
    (fun m ⟨h1, _, mC, σC', c', hA', hJ1, hJ2, hK'⟩ => ⟨h1, mC, σC', ⟨-48, []⟩, hK', hA', c', hJ1, hJ2⟩)
    (fun _ h _ => h) ?_
  · have hS := hres.mono_post (Q' := At (Ly).exe (Ly).endPc (MT) (FT m0 σC)
        (rX (tpXa ((MSU) [FR]) (TV)) (Ly).lab (LB) (MT) (mRdJ0 ((J') (TOP)) σC) .abort)) fun s c h => by
      rcases h with ⟨e, -⟩ | ⟨y, h⟩
      · exact e.elim
      · cases y
        · obtain ⟨-, -, -, -, σ, -, -, hJ⟩ := h
          exact hJ.elim
        · exact h
    -- the thread pointer kept; at `unXa (msBotHg OX [FR]) r1Of`, then `keepUn`, lifted to `[FR]`
    have hS0 := Spike.Lib.X64.Flow.SegW.keepTPN' rfl hS fun _ _ h ht => h ht
    have hS1 := Spike.Lib.X64.WakePh.StartH0X.SegW.mono_xa (ms' := unXa ((MSB) [FR]) (R1)) hS0 rfl
      fun _ _ _ _ _ h hU' => ⟨h.1, h.2 hU'⟩
    have hS2 := Spike.Lib.X64.KeepUn.SegW.keepUn rfl hS1 fun _ _ _ s' hk hs => by
      obtain ⟨-, pm, rfl⟩ := hk; exact Spike.Lib.X64.KeepUn.take_un pm hd hw1 hwS hs
    have hL := Spike.Lib.SegWS.liftS (W := fun s c fs => WP s c fs) (ms := MSB) [FR] hS2 fun _ _ h => h
    -- the abort closed; the take as `TakeCKS`; `WSg OX` as `W0Hg OX`
    have hC := Spike.Lib.X64.HelloPh.RdHAbX.hello_rd_hab_closedX hpw IH (Ctx := Ctx) (ls0 := ls0)
      (J1 := fun σC => mRdJ0 ((J') (TOP)) σC) hpa hhp hlo0 hA13 hhabctlRd
    refine Spike.Lib.X64GfpS.gfpS_of_segWS (Spike.Lib.X64.WakePh.Land5.segWS_mono_W
      (Spike.Lib.X64.WakePh.Land5.segWS_mono_K ((hL.mono_post ?_).seq hC)
        fun s c fs hW s' => Spike.Lib.X64.HelloPh.StartH0B.takeCKS_iffH hpw IH hW.2.1)
      (W' := W0Hg (asm := asm) hpw IH (OX) E DtW Ctx (ls0T ls0) (FR)) fun s c fs h => ?_) s c [FR]
      ⟨⟨⟨hAt, hT⟩, hU⟩, rfl⟩
    · rintro s c fs ⟨⟨⟨hX, -⟩, -⟩, hfs⟩
      obtain ⟨he, hn, hdc, hpc, σ, hAb, hF, hX0, hsl, q', hq', hJ⟩ := hX
      exact ⟨⟨TOP, m0, σC, ⟨he, hn, hdc, hpc, σ, hAb, hF, hX0, hsl,
        ⟨q'.1, { q'.2 with }⟩, hq', hJ⟩⟩, hfs⟩
    · show Spike.Lib.X64.WakeWf.W0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ s c fs
      rw [Spike.Lib.X64.Flow.Worker.Wake.AbOffW.marks_target (Ly) hpL]; exact h
  -- the allocator's heap abort lands at `wc_rodata`'s
  rintro ⟨⟩ σx c' σC' hx ⟨c, ⟨⟨σe, hJe, -, -⟩, -⟩, ⟨hc, -⟩⟩
  obtain ⟨h2, hfull, hs⟩ := hx
  refine .inr ⟨.abort, rfl, by show Spike.Lib.X64.SO.le ⟨-208, []⟩ ⟨-48 + -160, []⟩ = true; decide, h2, ?_,
    ⟨q, hqT⟩, hfull, σe, hc ▸ hJe⟩
  show (Spike.Lib.X64.leave (aR (MT)) (-48) σC' σx).slot (-208) = _
  simp only [Spike.Lib.X64.leave]
  rw [ite_eq_left (by simp only [Region.Off, Region.callee]; omega)]
  exact hs

/-! ## Level 1's statement at any fragment -/

/-- **Level 1's entry at `own` does not read the fragment** (AArch64 `RootL1F.rdLandH_xa` at `own`): `RdLandHg own`
moves between any two fragments `I`, `I'` (only the call's `Call.OK`, carried over field by field). -/
theorem rdLandHg_xa {own : Spike.Lib.X64Consumer.Own} {E : Entry} {rd : TermRun.Word → Prop}
    {I I' : Spike.Lib.X64ConsumerS.InvS} {ls : Lsize} {J1 : FAS → FAS → Spike.Lib.Ctl → Prop}
    {l : WeakMem.AllocLabel} {b w : Nat} {s : State} {c : Spike.Lib.Ctl}
    (h : RdLandHg (asm := asm) hpw i0 own E rd I ls J1 l b w s c) :
    RdLandHg (asm := asm) hpw i0 own E rd I' ls J1 l b w s c := by
  obtain ⟨v, m0, σC, q, F', h1, h2, h3, hu, ht⟩ := h
  exact ⟨v, m0, σC, ⟨q.1, { q.2 with }⟩, F', h1, h2, h3, hu, ht⟩

/-- **Level 1's statement at `RdLandHg own` is at any fragment** (at `own`): `H1StmtHF` is
antitone in its entry, and `rdLandHg_xa`. -/
theorem h1_rdLandg_xa {own : Spike.Lib.X64Consumer.Own} {E : Entry} {rd : TermRun.Word → Prop}
    {I I' : Spike.Lib.X64ConsumerS.InvS} {ls : Lsize} {J1 : FAS → FAS → Spike.Lib.Ctl → Prop}
    {W1 : WeakMem.AllocLabel → Nat → Nat → FragS isa} {K : State → State → Prop} {ar : Spike.Lib.Arena}
    {L0 : Lbl} {ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isa} {L : RuntimeLayout}
    {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa} {fr : List TermRun.Frame}
    (hs : Spike.Lib.X64HelloPreA.H1StmtHF W1 K ar L0 ms1 L (RdLandHg (asm := asm) hpw i0 own E rd I ls J1) inv1 fr) :
    Spike.Lib.X64HelloPreA.H1StmtHF W1 K ar L0 ms1 L (RdLandHg (asm := asm) hpw i0 own E rd I' ls J1) inv1 fr :=
  fun l b n hl hb => ⟨(hs l b n hl hb).1, fun s c hr => (hs l b n hl hb).2.1 s c (rdLandHg_xa hpw i0 hr),
    (hs l b n hl hb).2.2⟩

/-! ## The root's level 0 at `CXU` -/

set_option hygiene false in
/-- rodata's level-0 context at `OX` (`rd := True`). -/
local notation "CX" => CtxRdHg (asm := asm) hpw i0 E (fun _ => True) ls (OX)

set_option hygiene false in
/-- `I3` with its `inv0` disjunct `⊥` at `rd := True`. -/
local notation "IBT" => I3 (AR) (LB) (ls0T ls) (fun _ _ _ => False) inv1 inv2

set_option hygiene false in
local notation "MSBT" => msBotHg (asm := asm) hpw IH E (fun _ => True) ls inv1 inv2 (OX)

set_option maxHeartbeats 1600000 in
/-- **`HLandRdUg OX` at the root** (`hlandRd_UX` at `Ctx := CX`, `rd := True`, `ls0 := ls`; `hrd` by
`HrdRootX.hrd_RdHX`). -/
theorem hlandRd_rootX (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some SccCode.helloCells) (hlo0 : Λ0.code.lo = lo)
    (hc : Spike.Lib.X64.Rt.CtrZ o) (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    (hm : (Ly).Λ.imms Spike.Lib.X64HelloRodataSrc.eB "m" 0 = some 2)
    {W1 : WeakMem.AllocLabel → Nat → Nat → FragS isa} {K : State → State → Prop}
    {ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isa}
    {I : Spike.Lib.X64ConsumerS.InvS}
    (h1 : Spike.Lib.X64HelloPreA.H1StmtHF W1 K (AR) (LB) ms1 (Ly)
      (RdLandHg (asm := asm) hpw i0 (OX) E (fun _ => True) I ls (fun σC => mRdJ0 ((J') (TOP)) σC)) inv1 [FR])
    (hhabctlRd : ∀ σC, Spike.Lib.X64.HelloPh.HabCtlRd.HabCtlRdH ((MSBT) [FR]) (Ly).lab helloSrc (Ly).Λ (LB)
      (MT) (AR) [FR] (mRdJ0 ((J') (TOP)) σC)) :
    HLandRdUg (asm := asm) hpw i0 E (fun _ => True) ls (OX)
      (inv0Hg (asm := asm) hpw IH E (fun _ => True) (CX) ls ls (FR) inv1 inv2 (OX)) :=
  hlandRd_UX hpw i0 E (fun _ => True) ls (CX) ls inv1 inv2 hpa hhp hlo0 hc hA13
    (Spike.Lib.X64.HelloPh.HrdRootX.hrd_RdHX hpw i0 E (fun _ => True) (IBT) ls hpa hhp hlo0 hc hA13 hm (ls0 := ls))
    (h1_rdLandg_xa hpw i0 h1) hhabctlRd

variable {W1 : WeakMem.AllocLabel → Nat → Nat → FragS isa}
  {W2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa}

set_option hygiene false in
/-- The root's instance data at `OX`, `Ctx := CtxU CX`, `frM := frH c0S.env`, both levels at `ls`. -/
local notation "DX" => helloDRg (asm := asm) hpw IH (OX) E (CtxU hpw i0 (CX)) ls (FR) W1 inv1 W2 inv2

/-- **`hW0` at `helloDRg … OX` with `Ctx := CtxU CX`** (AArch64 `A64HelloLandRU.hW0_RdU`, here at `OX`): the
counter row by `RootUL.ctrRow_ofFTU`, its tail `hR` (`HLandRdUg OX` in `inv0Hg … CX … OX`) lifted by `inv0_upHg`
with `U r1Of` kept by the add; `hnew` vacuous (the add writes the counter, `CtrF.ctrAtF_wr`). -/
theorem hW0_RdUX (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some SccCode.helloCells)
    (hR : HLandRdUg (asm := asm) hpw i0 E (fun _ => True) ls (OX)
      (inv0Hg (asm := asm) hpw IH E (fun _ => True) (CX) ls ls (FR) inv1 inv2 (OX))) :
    ∀ s c fs, (DX).inv0 s c fs → (DX).W0 s c fs →
      SFactsACH (Ly).Λ (μE) helloSrc (DX).rd (DX).G (DX).own (DX).ar (Spike.Lib.X64HelloO.IH (DX)) (DX).L0
        (DX).ls0 s c fs (DX).Dt (Spike.Lib.X64.WriteAb.Ab (Ly).lab) (DX).Cl
        (Spike.Lib.X64.Hello.ThreadsAb.AcH (Ly).lab Spike.Lib.X64.HelloPh.StartWf.pfxM) := by
  haveI := (Ly).valid
  obtain ⟨hp, hend, hin⟩ := Spike.Lib.X64.HelloPh.LandR.hcode_H hpw i0 hpa hhp
  exact Spike.Lib.X64.WakeWf.hW0
    (fun _ _ _ _ hC _ _ _ hr _ =>
      Spike.Lib.X64.HelloPh.RootUL.ctrRow_ofFTU hp hend hin (fun _ => rfl)
        (fun fs ms0 R F q hms hG hok s c hA ht hu => .inl ⟨rfl, rfl,
          inv0_upHg hpw i0 (OX) E (fun _ => True) (CX) ls (FR) inv1 inv2 s c fs
            (hR fs ms0 R F q hms hG hok s c hA hu ht) hu⟩)
        hC.1.1 hC.1.2 hC.2 hr)
    (fun s c fs _ hC hW _ _ _ _ _ _ _ =>
      (hW (Spike.Lib.X64.HelloPh.CtrF.ctrAtF_wr hp hend hin (fun _ => rfl) s c fs hC.1.1)).elim)

set_option maxHeartbeats 1600000 in
/-- **The root's `hW0` at `OX`** (`hW0_RdUX` with `hlandRd_rootX`): level 1's `h1` at `RdLandHg OX` and
`hhabctlRd` at `msBotHg OX`, and the loader's facts. -/
theorem hW0_rootX (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some SccCode.helloCells) (hlo0 : Λ0.code.lo = lo)
    (hc : Spike.Lib.X64.Rt.CtrZ o) (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    (hm : (Ly).Λ.imms Spike.Lib.X64HelloRodataSrc.eB "m" 0 = some 2)
    {W1' : WeakMem.AllocLabel → Nat → Nat → FragS isa} {K : State → State → Prop}
    {ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isa}
    {I : Spike.Lib.X64ConsumerS.InvS}
    (h1 : Spike.Lib.X64HelloPreA.H1StmtHF W1' K (AR) (LB) ms1 (Ly)
      (RdLandHg (asm := asm) hpw i0 (OX) E (fun _ => True) I ls (fun σC => mRdJ0 ((J') (TOP)) σC)) inv1 [FR])
    (hhabctlRd : ∀ σC, Spike.Lib.X64.HelloPh.HabCtlRd.HabCtlRdH ((MSBT) [FR]) (Ly).lab helloSrc (Ly).Λ (LB)
      (MT) (AR) [FR] (mRdJ0 ((J') (TOP)) σC)) :
    ∀ s c fs, (DX).inv0 s c fs → (DX).W0 s c fs →
      SFactsACH (Ly).Λ (μE) helloSrc (DX).rd (DX).G (DX).own (DX).ar (Spike.Lib.X64HelloO.IH (DX)) (DX).L0
        (DX).ls0 s c fs (DX).Dt (Spike.Lib.X64.WriteAb.Ab (Ly).lab) (DX).Cl
        (Spike.Lib.X64.Hello.ThreadsAb.AcH (Ly).lab Spike.Lib.X64.HelloPh.StartWf.pfxM) :=
  hW0_RdUX hpw i0 E ls inv1 inv2 hpa hhp (hlandRd_rootX hpw i0 E ls inv1 inv2 hpa hhp hlo0 hc hA13 hm h1 hhabctlRd)

set_option maxHeartbeats 1600000 in
/-- **The root's `hst0` at `OX` and `CtxU CX`** (`RootH0.hstHg`'s): `StartH0XR.hst0_XRc` at `rd := True`,
`ls0 := ls`, with `hWe` by `WeRootX.hWe_rootX`, `hq` by `Hq0.hq0_H` (its `Call.OK` carried over field by field),
`hctr2` by `X64HelloCtr2.hctr2_H`; lifted to `CtxU CX` by `hst0_UHg`. -/
theorem hst0_rootX (hE : E.Ok (Ly).Λ) (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some SccCode.helloCells) (hlo0 : Λ0.code.lo = lo)
    (hstat : Λ0.static = fun _ => none) (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    (hc : Spike.Lib.X64.Rt.CtrZ o) (hm : (Ly).Λ.imms Spike.Lib.X64HelloRodataSrc.eB "m" 0 = some 2)
    (hpin2 : (Ly).pinA.toNat + 200 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    {W1' : WeakMem.AllocLabel → Nat → Nat → FragS isa} {K : State → State → Prop}
    {ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isa}
    {I : Spike.Lib.X64ConsumerS.InvS}
    (h1 : Spike.Lib.X64HelloPreA.H1StmtHF W1' K (AR) (LB) ms1 (Ly)
      (RdLandHg (asm := asm) hpw i0 (OX) E (fun _ => True) I ls (fun σC => mRdJ0 ((J') (TOP)) σC)) inv1 [FR])
    (hhabctlRd : ∀ σC, Spike.Lib.X64.HelloPh.HabCtlRd.HabCtlRdH ((MSBT) [FR]) (Ly).lab helloSrc (Ly).Λ (LB)
      (MT) (AR) [FR] (mRdJ0 ((J') (TOP)) σC)) :
    SegWS (W0Hg (asm := asm) hpw IH (OX) E DtW (CtxU hpw i0 (CX)) (ls0T ls) (FR))
      (TakeCKS (AX) (Spike.Lib.X64.HelloPh.ClH (Ly))) helloSrc (LB) (MSBT) (StartPH hpw IH E)
      (fun _ _ _ => False) :=
  hst0_UHg hpw i0 (OX) E (fun _ => True) (CX) ls (FR) inv1 inv2 hE hA13
    (Spike.Lib.X64.HelloPh.StartH0XR.hst0_XRc (asm := asm) hpw i0 E hE (rd := fun _ => True) (ls0 := ls) (ls := ls)
      hpa hhp hlo0 hstat hA13 (Spike.Lib.X64HelloCtr2.hctr2_H hpw IH hA13) hc hm
      (Spike.Lib.X64.HelloPh.WeRootX.hWe_rootX hpw i0 hpa hhp hlo0 hA13 E (fun _ => True) ls ls)
      (fun σC σ c h => by
        obtain ⟨q, hq, h'⟩ := Spike.Lib.X64.HelloPh.Hq0.hq0_H (asm := asm) hpw i0 hstat hc hpin2 (E := E)
          (rd := fun _ => True) (I := IBT) (ls := ls) (fs := [FR]) σC σ c h
        exact ⟨q, { hq with }, h'⟩)
      (h1_rdLandg_xa hpw i0 h1) hhabctlRd)

end Spike.Lib.X64.HelloPh.RootL0X

/-! ## Axioms -/

/-- info: 'Spike.Lib.X64.HelloPh.RootL0X.rdLandHg_xa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootL0X.rdLandHg_xa

/-- info: 'Spike.Lib.X64.HelloPh.RootL0X.h1_rdLandg_xa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootL0X.h1_rdLandg_xa

/-- info: 'Spike.Lib.X64.HelloPh.RootL0X.takeU_Hg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootL0X.takeU_Hg

/-- info: 'Spike.Lib.X64.HelloPh.RootL0X.inv0_upHg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootL0X.inv0_upHg

/-- info: 'Spike.Lib.X64.HelloPh.RootL0X.hst0_UHg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootL0X.hst0_UHg

/-- info: 'Spike.Lib.X64.HelloPh.RootL0X.hlandRd_UX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootL0X.hlandRd_UX

/-- info: 'Spike.Lib.X64.HelloPh.RootL0X.hlandRd_rootX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootL0X.hlandRd_rootX

/-- info: 'Spike.Lib.X64.HelloPh.RootL0X.hW0_RdUX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootL0X.hW0_RdUX

/-- info: 'Spike.Lib.X64.HelloPh.RootL0X.hW0_rootX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootL0X.hW0_rootX

/-- info: 'Spike.Lib.X64.HelloPh.RootL0X.hst0_rootX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootL0X.hst0_rootX
