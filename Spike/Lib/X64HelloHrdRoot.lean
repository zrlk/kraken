/-
**`wc_rodata`'s level obligations at hello's root** (x86-64; the twin of `Spike/Lib/A64HelloHrdRoot.lean`'s live
part): the root's `hrd`, `HrdS.hrd_WSHF` with every premise but the context discharged at the root's layout,
memory sides and choices, then lifted to `tpG` by `HrdTp.RdPreW.mapWK`.

The root's `hrd` (`LandRd.hlandRd_U`'s) asks `HelloRd.RdPreW` inside the start's level under main's thread
pointer, for every first-stack top `v`, caller's memory `m0` and state `σC`, at the root's memory side
`msUH … [FR]`. The start's frame condition `FS` pins `v` at the first stack's top; at any other `v` it holds for no
memory and the obligations are vacuous (`rdPreW_vac`). At the top, `hrd_WSHF`'s premises are the root's: the
layout's (`PlaceWX`), the source's and frame's (`HrdR`), the arena's (`HrdArena`), the limit word
(`RuntimeLayout.words_mapped`, `HrdR.hun_FS`); the context is the one premise left (`hctx`), under main's thread
pointer: `W0` is monotone in its context (`WakePh.RootUL.w0_mono`), so inside `tpG` the guard is discharged.

- `rdPreW_vac`: `RdPreW` at a frame condition holding for no memory.
- `hrd_R`: the root's `hrd` at any context `Ctx`, given `hctx` under the thread pointer at `msUH … [FR]`.
- `hrd_RdH`: at `LandRU.CtxRdH` (`hW0_RdU`'s), no context premise left.

## Unlike AArch64

- `scc_rt_main`'s region at the new stack's base `v` is `MainGlue.RS helloLsw v` (AArch64 `swR v (-helloLsw) 0`),
  and `wc_rodata`'s caller's entry invariant `rdJH` takes it, so `J'` depends on `v` (as `LandRd.hlandRd_U`).
- `hrd_WSHF` asks the region's `OK` and 8-alignment (`fstable_FS`'s `RS` and the first stack's alignment;
  AArch64 `hok`, `hal` at 16) and `8 ≤ R.hi`; the allocator's return is `.Lwc_rodata.x15` with `CallerCells`
  reaching `8` (AArch64 `.L19_wc_rodata.sp0`, `0`).
- The thread pointer is `%fs`'s base `tpOf (tcbS Ly)` (AArch64 `TPIDR_EL0`); the loader's facts are `cellsOf`.
- `rdPreW_vac`'s prologue is x86-64's five-node `XProW` (AArch64 `ProW`, four).
- AArch64's `hrd_RH` (at `Land.CtxRH`) is dead and not twinned.
-/
import Spike.Lib.X64HelloHrdArena
import Spike.Lib.X64HelloHrdS
import Spike.Lib.X64HelloHrdTp
import Spike.Lib.X64HelloLandRU
import Spike.Lib.X64HelloHrdR
import Spike.Lib.X64WakeRootUL
import Spike.Lib.X64WakeTP
import Spike.Lib.X64WakeHClC

namespace Spike.Lib.X64.HelloPh.HrdRoot

variable {asm : Scc.Sem.X64.Asm}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Entry ValRep)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lsize)
open Spike.Lib (FragS Frag MemSide Region PlaceWX)
open Spike.Lib.X64 (At)
open Spike.Lib.X64.Flow.Ret0 (CallerCells tpOf)
open Spike.Lib.X64.Flow.Hello1 (mR mF mRdJ0 aR)
open Spike.Lib.X64.Flow.HelloRd (RdCtx RdPreW)
open Spike.Lib.X64.WakeTP (tpG)
open Spike.Lib.X64.HelloPh (lo)
open Spike.Lib.X64.WakeWf (DtW)
open Spike.Lib.X64.WakePh.MainGlue (FS JS RS tcbS topS)
open Spike.Lib.X64.WakePh.WcWfR (blkW_vac nodeW_vac allocW_vac)
open Spike.Lib.X64.Alloc (Call N)
open Spike.Lib.X64.KeepTP (TP)
open Spike.Lib.X64.HelloPh.StartGlue (X0WH)
open Spike.Lib.X64.HelloPh.StartH0G (helloLsw)
open Spike.Lib.X64.HelloPh.StartH0U (msUH)
open Spike.Lib.X64.HelloPh.StartWcS (rdJH WS)
open Spike.Lib.X64.HelloPh.C0S (c0S)
open Spike.Lib.X64.HelloPh.LandRU (CtxRdH)
open Spike.Lib.X64WakeLoadT (L0T ls0T)
open Spike.Lib.X64HelloSrc (helloSrc)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.X64.AS

/-- **`wc_rodata` up to the allocator's return at a frame condition holding for no memory** (`WcWfR.blkW_vac`,
`nodeW_vac`, `allocW_vac` per field). -/
theorem rdPreW_vac {W : Frag isa} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {F : MachineData → Prop} {ms : MemSide isa} {J0 J1 : FAS → Spike.Lib.Ctl → Prop}
    (hF : ∀ m, ¬ F m) : RdPreW W K exe endPc R F ms J0 J1 :=
  ⟨⟨blkW_vac hF, blkW_vac hF, nodeW_vac hF, blkW_vac hF, blkW_vac hF⟩, blkW_vac hF,
    fun _ _ _ => allocW_vac fun m h => hF m h.1⟩

section Root

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (rd : TermRun.Word → Prop) (I : Spike.Lib.X64ConsumerS.InvS) (ls : Lsize)

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
local notation "RS0" => Spike.Lib.X64.Rt.rS0 (Ly)

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

set_option hygiene false in
local notation "AX" => (Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL

set_option hygiene false in
/-- main's frame at the root. -/
local notation "FR" => Spike.Lib.X64HelloRdCf.frH c0S.env

set_option hygiene false in
local notation "KR" => Spike.Lib.X64.PhRec.K (Ly) (RS0)

set_option hygiene false in
/-- `wc_rodata`'s caller's entry invariant at the new stack's base `v` (`LandRd`'s `J'`). -/
local notation "J'" => fun v : BitVec 64 => rdJH (Ly).lab (RS helloLsw v) (JS (Ly) 0#64 c0S)

set_option hygiene false in
/-- The first stack's top. -/
local notation "TOP" => topS (Ly) 0#64

set_option hygiene false in
/-- main's thread pointer. -/
local notation "TV" => tpOf (tcbS (Ly))

set_option hygiene false in
/-- The root's memory side under main's frame (`hlandRd_U`'s `MSU [FR]`, any fragment `I`). -/
local notation "MSU" => msUH (asm := asm) hpw i0 E rd I ls [FR]

set_option hygiene false in
/-- The start's level at the root's choices (`hlandRd_U`'s `WP`). -/
local notation "WP" => WS (Ly) NT (AR) helloSrc DtW (Spike.Lib.X64.HelloPh.ClH (Ly)) Ctx (LB) (ls0T ls0) (FR)
  (X0WH (Ly) (AX))

/-- **The root's `hrd` at any context** (module doc): `wc_rodata` up to the allocator's return inside the start's
level under main's thread pointer, from `scc_rt_main`'s call at the first stack's top, for every `v`, `m0`, `σC`,
at `msUH … [FR]`. The context at the counter add is the one premise (`hctx`, under main's thread pointer). -/
theorem hrd_R (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some SccCode.helloCells) (hlo0 : Λ0.code.lo = lo)
    (hc : Spike.Lib.X64.Rt.CtrZ o)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    (hm : (Ly).Λ.imms Spike.Lib.X64HelloRodataSrc.eB "m" 0 = some 2) {Ctx : FragS isa} {ls0 : Lsize}
    (hctx : ∀ (v : BitVec 64) (m0 : MachineData) (σC : FAS), ∀ q : Call, q.OK (MSU) (Ly).lab →
      q.ra = ((Ly).lab ".Lwc_rodata.x15").toBitVec →
      ∀ s c, At (Ly).exe (Ly).endPc (aR (mR (RS helloLsw v)))
        (fun m => mF (RS helloLsw v) (FS (Ly) (RS0) helloLsw 0#64 v) m0 σC m ∧
          CallerCells (mR (RS helloLsw v)) (-48) (-160) 8 m ∧
          RdCtx (MSU) (Ly).lab (mR (RS helloLsw v)) (mRdJ0 ((J') v) σC) (mRdJ0 ((J') v) σC) q m)
        (N (Ly).lab (MSU) q .rmw) s c → TP (TV) s → Ctx s c [FR]) :
    ∀ v m0 σC, RdPreW (tpG (TV) fun s c => WP s c [FR]) KR (Ly).exe (Ly).endPc (mR (RS helloLsw v))
      (mF (RS helloLsw v) (FS (Ly) (RS0) helloLsw 0#64 v) m0 σC) (MSU) (mRdJ0 ((J') v) σC)
      (mRdJ0 ((J') v) σC) := by
  intro v m0 σC
  -- the frame condition pins `v` at the first stack's top
  by_cases hv : v = TOP
  case neg => exact rdPreW_vac fun m hm => hv hm.1.1.2.1.1
  subst hv
  -- the layout's facts
  have hprog : (Ly).prog = SccCode.helloCells := Option.some.inj (hpa.symm.trans hhp)
  have hlo : (Ly).Λ.code.lo = lo := hlo0
  have hlab := Spike.Lib.X64HelloOInit.hlab_H hpw IH hpa hhp hlo0
  have hΛ : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName :=
    Spike.Lib.PlaceWX.abortLbl_of_placeWX (Spike.Lib.PlaceWX.link IH hpw)
  have hsite := Spike.Lib.X64.HelloPh.siteH hprog hlo hlab
  have hX0 := Spike.Lib.X64.HelloPh.StartGlue.x0WH_of_freeNH (L := Ly) (a := AX) hlab rfl
  have hcl := Spike.Lib.X64.HelloPh.ClH.cl (L := Ly)
  -- the region: `scc_rt_main`'s at the first stack's top, 8-aligned
  obtain ⟨hok, hR, -⟩ := Spike.Lib.X64.HelloPh.Land.fstable_FS hpw i0
  have hbd : (Spike.Lib.X64.Flow.Ret0.stacksA (Ly).lab).toNat + 32768 < 2 ^ 64 :=
    Spike.Lib.X64WakeHClC.hbd_W hpw IH
  have hal : (Spike.Lib.X64.Flow.Ret0.stacksA (Ly).lab).toNat % 16 = 0 := by
    rw [(Ly).lab_stacks]; exact (Ly).stacks_al
  have hb0 : ((RS helloLsw (TOP)).base.toNat : Int) = (TOP).toNat + (-8 - 0) :=
    Region.callee_base hok (by show (-helloLsw : Int) ≤ -8 - 0 + (8 - helloLsw); decide) (by decide)
      (by show (-8 - 0 : Int) < 0; decide)
  have htop : (TOP).toNat = (Spike.Lib.X64.Flow.Ret0.stacksA (Ly).lab).toNat + 16384 := by
    simp only [topS, BitVec.add_zero, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hR8 : (RS helloLsw (TOP)).base.toNat % 8 = 0 := by omega
  -- `hrd_WSHF` at the context guarded by the thread pointer, then the guard discharged inside `tpG`
  have h := Spike.Lib.X64.HelloPh.HrdS.hrd_WSHF (rS := RS0) (a := NT) (ar := AR) (Dt := DtW)
    (Cl := Spike.Lib.X64.HelloPh.ClH (Ly)) (Ctx := fun s c fs => TP (TV) s → Ctx s c fs) (lbl := LB)
    (lsize := ls0T ls0) (X0 := X0WH (Ly) (AX)) hprog hlo hΛ hlab hsite hcl hX0 hR hR8
    (show (8 - helloLsw : Int) ≤ -288 by decide) (show (8 : Int) ≤ 8 by decide)
    (Spike.Lib.X64.HelloPh.HrdArena.hpool_U hpw i0) (ms := MSU) (J := JS (Ly) 0#64 c0S) (tp := TV)
    (w := TermRun.cst (.loc ⟨Spike.Lib.X64WakeT1.mainTidLbl 2, 0⟩ 0)) (env := c0S.env) (m0 := m0) (σC := σC)
    (Spike.Lib.X64.HelloPh.HrdR.hJ_JS hpw i0) Spike.Lib.X64.HelloPh.HrdR.hme_c0S hm ?hmr
    Spike.Lib.X64.HelloPh.HrdR.hun_FS
    (Spike.Lib.X64.HelloPh.HrdArena.hmp_U hpw i0)
    (Spike.Lib.X64.HelloPh.HrdArena.hmem_U hpw i0 hc)
    (Spike.Lib.X64.HelloPh.HrdArena.hno_U hpw i0 hA13)
    (fun q _ _ => Spike.Lib.X64.HelloPh.HrdArena.hX0a_U hpw i0 hpa hhp hlo0 q)
    (fun q hq hra s c hAt htp => hctx (TOP) m0 σC q hq hra s c hAt htp)
    (Spike.Lib.X64.HelloPh.HrdArena.hctr_U hpw i0) (Spike.Lib.X64.HelloPh.HrdArena.hheap_U hpw i0)
    (Spike.Lib.X64.HelloPh.HrdArena.hoff_U hpw i0) (Spike.Lib.X64.HelloPh.HrdArena.hnew_U hpw i0)
    (Spike.Lib.X64.HelloPh.HrdArena.hlt_U hpw i0 hc) (Spike.Lib.X64.HelloPh.HrdArena.h64_U hpw i0 hc)
  case hmr =>
    show Scc.Sem.Kernel.mapped _ false ⟨Spike.Lib.X64.Flow.Ret0.limA (tpOf (Spike.Lib.X64.Flow.Ret0.pinA
      (Ly).lab + 0#64 + 8#64)), 8⟩ = true
    rw [(Ly).lab_pin, Spike.Lib.X64.Rt.limA_tcb0]
    exact ((Ly).words_mapped _ ((Ly).fld_mem (i := 1) (by decide))).2.1
  exact Spike.Lib.X64.HelloPh.HrdTp.RdPreW.mapWK
    (fun s c hw hk => ⟨fun ht => Spike.Lib.X64.WakePh.RootUL.w0_mono hw fun hC => hC ht, hk⟩) h

/-- **The root's `hrd` at `LandRU.CtxRdH`** (`hW0_RdU`'s level-0 context): `hrd_R` at `LandRU.hctx_rdRH`. -/
theorem hrd_RdH (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some SccCode.helloCells) (hlo0 : Λ0.code.lo = lo)
    (hc : Spike.Lib.X64.Rt.CtrZ o)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    (hm : (Ly).Λ.imms Spike.Lib.X64HelloRodataSrc.eB "m" 0 = some 2) {ls0 : Lsize} :
    ∀ v m0 σC, RdPreW (tpG (TV) fun s c => WS (Ly) NT (AR) helloSrc DtW (Spike.Lib.X64.HelloPh.ClH (Ly))
        (CtxRdH (asm := asm) hpw i0 E rd ls) (LB) (ls0T ls0) (FR) (X0WH (Ly) (AX)) s c [FR])
      KR (Ly).exe (Ly).endPc (mR (RS helloLsw v)) (mF (RS helloLsw v) (FS (Ly) (RS0) helloLsw 0#64 v) m0 σC)
      (MSU) (mRdJ0 ((J') v) σC) (mRdJ0 ((J') v) σC) :=
  hrd_R hpw i0 E rd I ls hpa hhp hlo0 hc hA13 hm fun v m0 σC =>
    Spike.Lib.X64.HelloPh.LandRU.hctx_rdRH hpw i0 E rd ls hc rfl v m0 σC

end Root

end Spike.Lib.X64.HelloPh.HrdRoot

/-- info: 'Spike.Lib.X64.HelloPh.HrdRoot.rdPreW_vac' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.HrdRoot.rdPreW_vac

/-- info: 'Spike.Lib.X64.HelloPh.HrdRoot.hrd_R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.HrdRoot.hrd_R

/-- info: 'Spike.Lib.X64.HelloPh.HrdRoot.hrd_RdH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.HrdRoot.hrd_RdH
