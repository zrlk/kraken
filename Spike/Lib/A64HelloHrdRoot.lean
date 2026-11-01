/-
**`wc_rodata`'s level obligations at hello's root** (AArch64; the root's `hrd`, the `wc_rodata` half of the
counter context's plumbing: `HrdS.hrd_WSHF` with every premise but the context discharged at the root's layout,
memory sides and choices, then lifted to `tpG` by `HrdTp.rdPreW_tpG`). `m`'s immediate at `rodata`'s allocation
is asked of the layout (`hm`, as the root's other immediates), not of the table `i0`.

The root's `hrd` (`LandRd.hlandRd_U`'s, `StartH0U1.hst0_ofHU1_i0`'s) asks `HelloRd.RdPreW` inside the start's level
under main's thread pointer, for every first-stack top `v`, caller's memory `m0` and state `σC`, at the root's
memory side `msUH … [FR]`. The start's frame condition `FS` pins `v` at the first stack's top (`fstable_FS`); at any
other `v` it holds for no memory and the obligations are vacuous (`rdPreW_vac`). At the top, `hrd_WSHF`'s premises
are the root's: the layout's (`PlaceW`), the source's and frame's (`HrdR`), the arena's (`HrdArena`), the limit word
(`RuntimeLayout.words_mapped`, `HrdR.hun_FS`); the context is the one premise left (`hctx`), under main's thread
pointer as the producers give it (`Land.hctx_rdU`, `LandRU.hctx_rdRH`): `W0` is monotone in its context
(`RootUL.w0_mono`), so inside `tpG` the thread-pointer guard is discharged.

- `rdPreW_vac`: `RdPreW` at a frame condition holding for no memory.
- `hrd_R`: the root's `hrd` at any context `Ctx`, given `hctx` under the thread pointer at `msUH … [FR]`.
- `hrd_RH`, `hrd_RdH`: at `Land.CtxRH` (`HelloAssemblyRC`'s choice) and `LandRU.CtxRdH` (`hW0_RdU`'s), no
  context premise left.
-/
import Spike.Lib.A64HelloHrdArena
import Spike.Lib.A64HelloHrdR
import Spike.Lib.A64HelloHrdTp
import Spike.Lib.A64HelloLandRU

namespace Spike.Lib.A64.HelloPh.HrdRoot

variable {asm : String}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Entry)
open Scc.Sem.A64 (textProgram)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lsize)
open Spike.Lib (FragS Frag MemSide Region)
open Spike.Lib.A64.Flow (At swR)
open Spike.Lib.A64.Flow.Ret0 (CallerCells pinA)
open Spike.Lib.A64.Flow.Hello1 (mR mF mRdJ0 aR)
open Spike.Lib.A64.Flow.HelloRd (RdCtx RdPreW)
open Spike.Lib.A64.Flow.WakeWc (tpG)
open Spike.Lib.A64.WakePh (lo)
open Spike.Lib.A64.WakeWf (DtW)
open Spike.Lib.A64.WakePh.MainGlue (FS JS)
open Spike.Lib.A64.WakePh.WcWfR (blkW_vac nodeW_vac allocW_vac)
open Spike.Lib.A64.Alloc (Call N)
open Spike.Lib.A64.KeepTP (TP)
open Spike.Lib.A64.HelloPh.StartGlue (X0WH)
open Spike.Lib.A64.HelloPh.StartH0G (helloLsw)
open Spike.Lib.A64.HelloPh.StartH0U (msUH)
open Spike.Lib.A64.HelloPh.StartWcS (rdJH WS)
open Spike.Lib.A64.HelloPh.C0S (c0S)
open Spike.Lib.A64.HelloPh.Land (CtxRH)
open Spike.Lib.A64.HelloPh.LandRU (CtxRdH)
open Spike.Lib.WakeLoadT (L0T ls0T)
open Spike.Lib.HelloSrc (helloSrc)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.A64.Flow.AS

/-- **`wc_rodata` up to the allocator's return at a frame condition holding for no memory** (`WcWfR.blkW_vac`,
`nodeW_vac`, `allocW_vac` per field). -/
theorem rdPreW_vac {W : Frag isaLSE2} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {F : MachineData → Prop} {ms : MemSide isaLSE2} {J0 J1 : FAS → Spike.Lib.Ctl → Prop}
    (hF : ∀ m, ¬ F m) : RdPreW W K exe endPc R F ms J0 J1 :=
  ⟨⟨blkW_vac hF, nodeW_vac hF, blkW_vac hF, blkW_vac hF⟩, blkW_vac hF,
    fun _ _ _ => allocW_vac fun m h => hF m h.1⟩

section Root

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (rd : TermRun.Word → Prop) (I : Spike.Lib.A64ConsumerS.InvS) (ls : Lsize)

set_option hygiene false in
/-- The root's immediate table at the certificate's table `i0` (as `StartH0U`). -/
local notation "IH" => Spike.Lib.A64.HelloPh.C0S.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hpw IH

set_option hygiene false in
local notation "AR" => Spike.Lib.WakeOD.arW hpw IH

set_option hygiene false in
local notation "NT" => Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab

set_option hygiene false in
local notation "RS" => Spike.Lib.A64.Rt.rS0 (Ly)

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

set_option hygiene false in
local notation "AX" => (Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL

set_option hygiene false in
/-- main's frame at the root (`StartH0U`'s `FR`). -/
local notation "FR" => Spike.Lib.HelloRdCf.frH c0S.env

set_option hygiene false in
local notation "KR" => Spike.Lib.A64.PhRec.K (Ly) RS

set_option hygiene false in
/-- `wc_rodata`'s caller's entry invariant at the root (`StartH0U`'s `J'`). -/
local notation "J'" => rdJH (Ly).lab (JS (Ly) 0#64 c0S)

set_option hygiene false in
/-- The first stack's top. -/
local notation "TOP" => Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64

set_option hygiene false in
/-- main's thread pointer. -/
local notation "TV" => UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64)

set_option hygiene false in
/-- The root's memory side under main's frame (`hlandRd_U`'s `MSU [FR]`, any fragment `I`). -/
local notation "MSU" => msUH (asm := asm) hpw i0 E rd I ls [FR]

set_option hygiene false in
/-- The start's level at the root's choices (`hlandRd_U`'s `WP`). -/
local notation "WP" => WS (Ly) NT (AR) helloSrc DtW (Spike.Lib.A64.HelloPh.ClH (Ly)) Ctx (LB) (ls0T ls0) (FR)
  (X0WH (Ly) (AX))

/-- **The root's `hrd` at any context** (module doc): `wc_rodata` up to the allocator's return inside the start's
level under main's thread pointer, from `scc_rt_main`'s call at the first stack's top, for every `v`, `m0`, `σC`,
at `msUH … [FR]`. The context at the counter add is the one premise (`hctx`, under main's thread pointer, as
`Land.hctx_rdU`). -/
theorem hrd_R (hpa : textProgram asm = .ok o.prog) (hhp : textProgram asm = .ok SccCode.helloProg)
    (hlo0 : Λ0.code.lo = lo) (hc : Spike.Lib.A64.Rt.CtrZ o)
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    (hm : (Ly).Λ.imms Spike.Lib.HelloRodataSrc.eB "m" 0 = some 2) {Ctx : FragS isaLSE2} {ls0 : Lsize}
    (hctx : ∀ (v : BitVec 64) (m0 : MachineData) (σC : FAS), ∀ q : Call, q.OK (MSU) (Ly).lab →
      q.ra = ((Ly).lab ".L19_wc_rodata.sp0").toBitVec →
      ∀ s c, At (Ly).exe (Ly).endPc (aR (mR (swR v (-helloLsw) 0)))
        (fun m => mF (swR v (-helloLsw) 0) (FS (Ly) (RS) helloLsw 0#64 v) m0 σC m ∧
          CallerCells (mR (swR v (-helloLsw) 0)) (-48) (-160) 0 m ∧
          RdCtx (MSU) (Ly).lab (mR (swR v (-helloLsw) 0)) (mRdJ0 (J') σC) (mRdJ0 (J') σC) q m)
        (N (Ly).lab (MSU) q .rmw) s c → TP (TV) s → Ctx s c [FR]) :
    ∀ v m0 σC, RdPreW (tpG (TV) fun s c => WP s c [FR]) KR (Ly).exe (Ly).endPc (mR (swR v (-helloLsw) 0))
      (mF (swR v (-helloLsw) 0) (FS (Ly) RS helloLsw 0#64 v) m0 σC) (MSU) (mRdJ0 (J') σC) (mRdJ0 (J') σC) := by
  intro v m0 σC
  -- the frame condition pins `v` at the first stack's top
  by_cases hv : v = TOP
  case neg => exact rdPreW_vac fun m hm => hv hm.1.2.1.1
  subst hv
  -- the layout's facts
  have hp : o.prog = SccCode.helloProg := Except.ok.inj (hpa.symm.trans hhp)
  have hprog : (Ly).prog = SccCode.helloProg := hp
  have hlo : (Ly).Λ.code.lo = lo := hlo0
  have hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → (Ly).lab l = Int64.ofNat x :=
    fun l x h => Spike.Lib.PlaceW.hlab_ofPlaceW hpw IH l x (by rw [hlo, hp]; exact h)
  have hΛ : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName :=
    Spike.Lib.PlaceW.abortLbl_of_placeW (Spike.Lib.PlaceW.link IH hpw)
  have hsite := Spike.Lib.PlaceW.site_ofPlaceW hpw IH
  have hX0 := Spike.Lib.A64.HelloPh.StartGlue.x0WH_of_freeNH (L := Ly) (a := AX) hlab rfl
  have hcl := Spike.Lib.A64.HelloPh.ClH.cl (L := Ly)
  obtain ⟨hok, hal, -⟩ := Spike.Lib.A64.HelloPh.Land.fstable_FS hpw i0
  -- `hrd_WSHF` at the context guarded by the thread pointer, then the guard discharged inside `tpG`
  have h := Spike.Lib.A64.HelloPh.HrdS.hrd_WSHF (rS := RS) (a := NT) (ar := AR) (Dt := DtW)
    (Cl := Spike.Lib.A64.HelloPh.ClH (Ly)) (Ctx := fun s c fs => TP (TV) s → Ctx s c fs) (lbl := LB)
    (lsize := ls0T ls0) (X0 := X0WH (Ly) (AX)) hprog hlo hΛ hlab hsite hcl hX0 hok hal
    (show (-helloLsw : Int) ≤ -288 by decide) (show (0 : Int) ≤ 0 by decide)
    (Spike.Lib.A64.HelloPh.HrdArena.hpool_U hpw i0) (ms := MSU) (J := JS (Ly) 0#64 c0S) (tp := TV)
    (w := TermRun.cst (.loc ⟨Spike.Lib.WakeT1.mainTidLbl 2, 0⟩ 0)) (env := c0S.env) (m0 := m0) (σC := σC)
    (Spike.Lib.A64.HelloPh.HrdR.hJ_JS hpw i0) Spike.Lib.A64.HelloPh.HrdR.hme_c0S
    hm ?hmr Spike.Lib.A64.HelloPh.HrdR.hun_FS
    (Spike.Lib.A64.HelloPh.HrdArena.hmp_U hpw i0)
    (Spike.Lib.A64.HelloPh.HrdArena.hmem_U hpw i0 hc)
    (Spike.Lib.A64.HelloPh.HrdArena.hno_U hpw i0 hA13)
    (fun q _ _ => Spike.Lib.A64.HelloPh.HrdArena.hX0a_U hpw i0 hpa hhp hlo0 q)
    (fun q hq hra s c hAt htp => hctx (TOP) m0 σC q hq hra s c hAt htp)
    (Spike.Lib.A64.HelloPh.HrdArena.hctr_U hpw i0) (Spike.Lib.A64.HelloPh.HrdArena.hheap_U hpw i0)
    (Spike.Lib.A64.HelloPh.HrdArena.hoff_U hpw i0) (Spike.Lib.A64.HelloPh.HrdArena.hnew_U hpw i0)
    (Spike.Lib.A64.HelloPh.HrdArena.hlt_U hpw i0 hc) (Spike.Lib.A64.HelloPh.HrdArena.h64_U hpw i0 hc)
  case hmr =>
    rw [Spike.Lib.A64.Rt.pinA_lab0, Spike.Lib.A64.Rt.limA_tcb0]
    exact ((Ly).words_mapped _ ((Ly).fld_mem (by decide))).2.1
  exact Spike.Lib.A64.HelloPh.HrdTp.RdPreW.mapWK
    (fun s c hw hk => ⟨fun ht => Spike.Lib.A64.WakePh.RootUL.w0_mono hw fun hC => hC ht, hk⟩) h

/-- **The root's `hrd` at `Land.CtxRH`** (`HelloAssemblyRC`'s context): `hrd_R` at `Land.hctx_rdU`. -/
theorem hrd_RH (hpa : textProgram asm = .ok o.prog) (hhp : textProgram asm = .ok SccCode.helloProg)
    (hlo0 : Λ0.code.lo = lo) (hc : Spike.Lib.A64.Rt.CtrZ o)
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    (hm : (Ly).Λ.imms Spike.Lib.HelloRodataSrc.eB "m" 0 = some 2) {ls0 : Lsize} :
    ∀ v m0 σC, RdPreW (tpG (TV) fun s c => WS (Ly) NT (AR) helloSrc DtW (Spike.Lib.A64.HelloPh.ClH (Ly))
        (CtxRH (asm := asm) hpw i0 E rd ls) (LB) (ls0T ls0) (FR) (X0WH (Ly) (AX)) s c [FR])
      KR (Ly).exe (Ly).endPc (mR (swR v (-helloLsw) 0))
      (mF (swR v (-helloLsw) 0) (FS (Ly) RS helloLsw 0#64 v) m0 σC) (MSU) (mRdJ0 (J') σC) (mRdJ0 (J') σC) :=
  hrd_R hpw i0 E rd I ls hpa hhp hlo0 hc hA13 hm fun v m0 σC =>
    Spike.Lib.A64.HelloPh.Land.hctx_rdU hpw i0 E rd ls hc I v m0 σC

/-- **The root's `hrd` at `LandRU.CtxRdH`** (`hW0_RdU`'s level-0 context): `hrd_R` at `LandRU.hctx_rdRH`. -/
theorem hrd_RdH (hpa : textProgram asm = .ok o.prog) (hhp : textProgram asm = .ok SccCode.helloProg)
    (hlo0 : Λ0.code.lo = lo) (hc : Spike.Lib.A64.Rt.CtrZ o)
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    (hm : (Ly).Λ.imms Spike.Lib.HelloRodataSrc.eB "m" 0 = some 2) {ls0 : Lsize} :
    ∀ v m0 σC, RdPreW (tpG (TV) fun s c => WS (Ly) NT (AR) helloSrc DtW (Spike.Lib.A64.HelloPh.ClH (Ly))
        (CtxRdH (asm := asm) hpw i0 E rd ls) (LB) (ls0T ls0) (FR) (X0WH (Ly) (AX)) s c [FR])
      KR (Ly).exe (Ly).endPc (mR (swR v (-helloLsw) 0))
      (mF (swR v (-helloLsw) 0) (FS (Ly) RS helloLsw 0#64 v) m0 σC) (MSU) (mRdJ0 (J') σC) (mRdJ0 (J') σC) :=
  hrd_R hpw i0 E rd I ls hpa hhp hlo0 hc hA13 hm fun v m0 σC =>
    Spike.Lib.A64.HelloPh.LandRU.hctx_rdRH hpw i0 E rd ls hc rfl v m0 σC

end Root

end Spike.Lib.A64.HelloPh.HrdRoot

/-- info: 'Spike.Lib.A64.HelloPh.HrdRoot.rdPreW_vac' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.HrdRoot.rdPreW_vac

/-- info: 'Spike.Lib.A64.HelloPh.HrdRoot.hrd_R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.HrdRoot.hrd_R

/-- info: 'Spike.Lib.A64.HelloPh.HrdRoot.hrd_RH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.HrdRoot.hrd_RH

/-- info: 'Spike.Lib.A64.HelloPh.HrdRoot.hrd_RdH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.HrdRoot.hrd_RdH
