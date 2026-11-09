/-
**The root's `hM`: `wc_main`'s box counter add's tail at level 1, in level 1's invariant** (x86-64; the twin of
`Spike/Lib/A64HelloLandM1U.lean`): `LandR1U.HLandM1U` at `inv1G (W1Rg … OX) XR … (MS1X I) ∧ U r1Of`, where
`OX := ownGHXW Ly ntA` are main's owned words with both TCB self words.

From the allocator's `c2` after the counter add of `wc_main`'s box call (`Land.GcM1H`: the first stack's top, the
caller's slot `-16` main's TCB, `wc_main`'s entry at `Level1I`'s `JrRL` and its caller's at `Jr1LH l b`):
- the allocator's rest, its exits resumed in `wc_main`'s frame, then `.x22`, to the heap abort at `wXA`
  (`HelloWc.hello_wc_n4_segWA`), at the level's memory sides `MS1X` at `invUH I` (`I` asked only with `r1Of`
  unmapped), with `wc_main`'s `hWp`/`hWs` (`MainWcL1Wj.hWp_L1PX`/`hWs_L1PX`), the box's words and cell
  (`Level1M.hmem0_level1g`, `MainWcL1Q.hbox_L1`/`hcell0_L1`) and its landing (`MainWcL1A.hxa_IUX`, from `HLand2U`
  at `I`'s `xa`);
- the heap abort closed (`Level1HAX.hello_hab_closedLAX`, its controls `HabCtlA.habCtlHA_jr1L`);
- carried to the level's memory sides at `I` with `r1Of` unmapped (`KeepUnS.SegWS.mono_xa`/`keepUn`), so its start
  is in `inv1G` (`H1Gfp.inv1G_of_segWS`). `U r1Of` is `HLandM1U`'s own premise.

The landing is `I`'s, not `IH`'s: at the root `I` is the root's fragment.

- `HLandM1U.mono`, `inv1_I3`: the plug into the root's invariant (`I3`'s level-1 disjunct).
- `hlandM1_segX`: the allocator's tail from `c2` to `wXA` at `MS1X` at `invUH I`, inside `Level1I.W1Rg … OX`.
- `hLandM1U_IX`: `HLandM1U` at `inv1G (W1Rg … OX) … (MS1X I) ∧ U r1Of`, `HLandM1U` and its context `CtxR1H`
  unchanged; the box call's `OKB` is carried from `HLandM1U`'s side (at `ownGH`) field by field (it reads no own
  map).

## Differences from the AArch64 version

- The tail starts at the allocator's `c2` (AArch64 `n4`), the box call returns to `.Lwc_main.x0` (AArch64
  `.L22_wc_main.sp0`), the caller's pinned TCB slot is `-16` (AArch64 `-80`), and `wc_main`'s allocator region has
  `CallerCells … 8` (AArch64 `… 0`); `wc_main`'s region is `wcR (RS helloLsw TOP) helloD`, so `hello_wc_n4_segWA`
  takes no alignment premise.
- The loader's facts are the two parses `cellsOf asm` (AArch64 `textProgram`); the allocator's code is
  `LandR.hcode_H`'s.
- `hello_hab_closedLAX`'s post quantifies the first stack's top (`∃ v m1 σ1`), and `habCtlHA_jr1L` asks the
  memory side's counter, cells and units (`rfl` at the level's sides).
- `SegWS`'s `mono_K`/`mono_W` are `WakePh.Land5.segWS_mono_K`/`segWS_mono_W` (AArch64 `SegWS.mono_K`/`mono_W`).
- The level and its memory sides own `ownGHXW Ly ntA` (AArch64 `ownGH`: main owns no TCB word there).
-/
import Spike.Lib.X64HelloWcN4A
import Spike.Lib.X64HelloMainWcL1A
import Spike.Lib.X64HelloMainWcL1Wj
import Spike.Lib.X64HelloMainWcL1Wp
import Spike.Lib.X64HelloMainWcL1Q
import Spike.Lib.X64HelloLevel1M
import Spike.Lib.X64HelloLevel1IU
import Spike.Lib.X64HelloLevel1HA
import Spike.Lib.X64HelloHabCtlA
import Spike.Lib.X64HelloLandR1U
import Spike.Lib.X64HelloH1Gfp
import Spike.Lib.X64KeepUnS
import Spike.Lib.X64HelloLevel1HAX
import Spike.Lib.X64HelloMainWcL1XX
import Spike.Lib.X64HelloMainWcL1WjX

namespace Spike.Lib.X64.HelloPh.LandM1U

variable {asm : Scc.Sem.X64.Asm}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Entry)
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64ConsumerA (TakeCKS)
open Spike.Lib.X64.HelloPh (lo)
open Spike.Lib (FragS Frag MemSide SegWS SegW PlaceWX)
open Spike.Lib.X64 (At)
open Spike.Lib.X64.Flow.Ret0 (CallerCells tpOf)
open Spike.Lib.X64.Flow.Hello1 (mWC)
open Spike.Lib.X64.Flow.HelloM (wcJ0 wcR wcF JrT)
open Spike.Lib.X64.Flow.HelloWc (wARH WcCtxH wXA bXH)
open Spike.Lib.X64.Flow.HelloJr1 (JrRL)
open Spike.Lib.X64.WakePh.MainGlue (FS RS tcbS topS)
open Spike.Lib.X64.KeepTP (TP)
open Spike.Lib.X64.KeepUn (U unXa)
open Spike.Lib.X64.Alloc (Call)
open Spike.Lib.X64.HelloPh.StartGlue (X0WH)
open Spike.Lib.X64.HelloPh.StartH0G (helloD helloLsw)
open Spike.Lib.X64.HelloPh.StartH0U (invUH)
open Spike.Lib.X64.HelloPh.Level1I (W1Rg XR)
open Spike.Lib.X64.HelloPh.LandR1U (HLandM1U)
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.X64WakeLoadT (L0T ls0T)
open Spike.Lib.X64.HelloPh.C0S (c0S)
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.X64HelloMainPreSrc (newTerm)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.X64.AS

/-! ## `HLandM1U` is monotone; `I3`'s level-1 disjunct -/

/-- **`HLandM1U` is monotone in its target.** -/
theorem HLandM1U.mono {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
    {hpw : PlaceWX pcfg Λ0 o} {i0 : CoreTerm.Expr → String → Nat → Option Nat} {E : Entry}
    {rd : TermRun.Word → Prop} {ls : Lsize} {l : WeakMem.AllocLabel} {b n : Nat} {Q Q' : FragS isa}
    (h : HLandM1U (asm := asm) hpw i0 E rd ls l b n Q) (hQ : ∀ s c fs, Q s c fs → Q' s c fs) :
    HLandM1U (asm := asm) hpw i0 E rd ls l b n Q' :=
  fun fs ms0 R F q hms hG hok s c hAt htp hu => hQ s c fs (h fs ms0 R F q hms hG hok s c hAt htp hu)

/-- **Level 1's invariant is in `I3` at the level's labels** (`I3`'s second disjunct, the root's invariant at
`upd L0 l b`, `updN ls0 l n`). -/
theorem inv1_I3 {ar : Spike.Lib.Arena} {L0 : Lbl} {ls0 : Lsize} {inv0 : FragS isa}
    {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa}
    {inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa}
    {l : WeakMem.AllocLabel} {b n : Nat} (hl : L0 l = none) (hb : AllocLand ar.heap ar.cells b n) :
    ∀ s c fs, inv1 l b n s c fs →
      Spike.Lib.X64ConsumerA.I3 ar L0 ls0 inv0 inv1 inv2 (Spike.Lib.X64ConsumerA.upd L0 l b)
        (Spike.Lib.X64ConsumerA.updN ls0 l n) s c fs :=
  fun _ _ _ h => .inr (.inl ⟨l, b, n, hl, hb, rfl, rfl, h⟩)

/-! ## The allocator's tail -/

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (rd : TermRun.Word → Prop) (I : Spike.Lib.X64ConsumerS.InvS) (ls : Lsize)

set_option hygiene false in
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
local notation "L0" => L0T (Ly).Λ

set_option hygiene false in
/-- The take site's label. -/
local notation "AX" => (Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL

set_option hygiene false in
local notation "FR" => Spike.Lib.X64HelloRdCf.frH c0S.env

set_option hygiene false in
local notation "KR" => Spike.Lib.X64.PhRec.K (Ly) (RS0)

set_option hygiene false in
/-- The child's stack. -/
local notation "R1" => Spike.Lib.X64.Rt.PreChild.r1Of (Ly).lab

set_option hygiene false in
/-- main's thread pointer. -/
local notation "TV" => tpOf (tcbS (Ly))

set_option hygiene false in
/-- The first stack's top (the start's `v`). -/
local notation "TOP" => topS (Ly) 0#64

set_option hygiene false in
/-- The fragment `I` asked only with `r1Of` unmapped. -/
local notation "IU" => invUH hpw i0 I

set_option hygiene false in
/-- The level's memory sides at a fragment `J` after rodata's allocation of `l` at `b`, `n` words, at `fs`. -/
local notation "MS1" => fun (J : Spike.Lib.X64ConsumerS.InvS) (l : WeakMem.AllocLabel) (b n : Nat)
    (fs : List TermRun.Frame) =>
  Spike.Lib.X64ConsumerA.msOfA (Ly).Λ
    ((Scc.Sem.X64.target (Scc.Sem.X64.kernel 2) E).marks asm (Ly).Λ) rd
    (Spike.Lib.X64HelloGOf2H.gWH hpw IH (Spike.Lib.X64WakeHG.cTW hpw IH))
    (fun s _ => Spike.Lib.X64.HelloPh.ownGH (Ly) (NT) s)
    (AR) J (Spike.Lib.X64ConsumerA.upd (L0) l b) (Spike.Lib.X64ConsumerA.updN (ls0T ls) l n) fs

set_option hygiene false in
/-- `wc_main`'s region at the call. -/
local notation "RW" => wcR (RS helloLsw (TOP)) helloD

set_option hygiene false in
/-- `wc_main`'s frame condition at the caller's state `m1`, `σ1`. -/
local notation "FW" => wcF (RS helloLsw (TOP)) helloD (FS (Ly) (RS0) helloLsw 0#64 (TOP)) m1 σ1

set_option hygiene false in
/-- `wc_main`'s entry invariant at `Level1I`'s `Jr` (`Land.GcM1H`'s). -/
local notation "J0" => wcJ0 (mWC (Ly).lab σC (JrT (JrRL (Spike.Lib.X64ConsumerA.upd (L0) l b) c0S.env l) (TV)
  (RS helloLsw (TOP)))).J σ1

set_option hygiene false in
/-- `wc_main`'s caller's invariant at the box's `new` (`Land.Jr1LH`). -/
local notation "J1" => wcJ0 (mWC (Ly).lab σC (Spike.Lib.X64.HelloPh.Land.Jr1LH hpw i0 l b)).J σ1

set_option hygiene false in
/-- main's owned words before the spawn, at `scc_rt_nthreads`. -/
local notation "OX" => Spike.Lib.X64.HelloPh.ownGHXW (Ly) NT

set_option hygiene false in
/-- `MS1` at the owned words `OX`. -/
local notation "MS1X" => fun (J : Spike.Lib.X64ConsumerS.InvS) (l : WeakMem.AllocLabel) (b n : Nat)
    (fs : List TermRun.Frame) =>
  Spike.Lib.X64ConsumerA.msOfA (Ly).Λ
    ((Scc.Sem.X64.target (Scc.Sem.X64.kernel 2) E).marks asm (Ly).Λ) rd
    (Spike.Lib.X64HelloGOf2H.gWH hpw IH (Spike.Lib.X64WakeHG.cTW hpw IH))
    (fun s _ => Spike.Lib.X64.HelloPh.ownGHXW (Ly) (NT) s)
    (AR) J (Spike.Lib.X64ConsumerA.upd (L0) l b) (Spike.Lib.X64ConsumerA.updN (ls0T ls) l n) fs

/-! ## At `ownGHXW` -/

set_option maxHeartbeats 1600000 in
/-- **`hlandM1_seg` at `ownGHXW`** (module doc): from the allocator's `c2` of `wc_main`'s box call at the pinned
caller (the slot `-16` main's TCB, `hslot`) under main's thread pointer, a segment inside the level `W1Rg … OX` at
no frames to the heap abort at `wXA`, at the level's memory sides `MS1X` at `invUH I` (`MainWcL1Wj.hWp_L1PX`,
`hWs_L1PX`, `MainWcL1A.hxa_IUX`, `Level1M.hmem0_level1g`). -/
theorem hlandM1_segX (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some SccCode.helloCells)
    (hlo0 : Λ0.code.lo = lo) (hc : Spike.Lib.X64.Rt.CtrZ o)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    (hz : i0 newTerm "z" 0 = some 0)
    {l : WeakMem.AllocLabel} {b n : Nat} (hl : (L0) l = none)
    (hX : Spike.Lib.X64.HelloPh.LandR1U.HLand2U (asm := asm) hpw i0 E rd ls l b n ((MS1X) I l b n []).xa)
    {σC : FAS} (hslot : σC.slot (-16) = Spike.Lib.X64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64)
    (m1 : MachineData) (σ1 : FAS) {q : Call} (hq : q.OKB ((MS1X) (IU) l b n []) (Ly).lab)
    (hra : q.ra = ((Ly).lab ".Lwc_main.x0").toBitVec) :
    SegW (fun s c => W1Rg (asm := asm) hpw i0 E rd ls (OX) l b n s c []) (KR) helloSrc
      (Spike.Lib.X64ConsumerA.upd (L0) l b) ((MS1X) (IU) l b n [])
      (fun s c => At (Ly).exe (Ly).endPc (wARH (RW)) (fun m => (FW) m ∧ CallerCells (RW) (-144) (-160) 8 m ∧
          WcCtxH ((MS1X) (IU) l b n []) (Ly).lab (RW) (J0) (J1) q m)
        (Spike.Lib.X64.Alloc.N (Ly).lab ((MS1X) (IU) l b n []) q .c2) s c ∧ TP (TV) s)
      (fun s c => At (Ly).exe (Ly).endPc (RW) (FW) (wXA ((MS1X) (IU) l b n []) (Ly).lab (J1)) s c ∧ TP (TV) s) := by
  have hp : o.prog = SccCode.helloCells := Option.some.inj (hpa.symm.trans hhp)
  obtain ⟨hpS, hendS, -⟩ := Spike.Lib.X64.HelloPh.LandR.hcode_H hpw i0 hpa hhp
  have : Kraken.Executable.ValidLayout (Ly).exe := (Ly).valid
  obtain ⟨-, hok, hF0⟩ := Spike.Lib.X64.HelloPh.Land.fstable_FS hpw i0
  obtain ⟨hR, hF⟩ := Spike.Lib.X64.Flow.HelloM.wcR_ok (D := helloD) (by decide) (by decide) hok hF0
    (by show (8 - helloLsw : Int) ≤ -80 - helloD; decide) (by show (0 : Int) ≤ 8; decide) m1 σ1
  have hzL := Spike.Lib.X64.HelloPh.MainWcL1A.hzL hpw i0 hz
  have hJ := Spike.Lib.X64.HelloPh.MainWcL1Wp.hJ_L1 hpw i0 (l := l) (b := b) (σC := σC) (σ1 := σ1)
  have hcell := Spike.Lib.X64.HelloPh.MainWcL1Q.hcell0_L1 hpw IH
    (μ := (Scc.Sem.X64.target (Scc.Sem.X64.kernel 2) E).marks asm (Ly).Λ) (rd := rd)
    (own := fun s _ => Spike.Lib.X64.HelloPh.ownGHXW (Ly) (NT) s) (I := IU)
    (lbl := Spike.Lib.X64ConsumerA.upd (L0) l b) (lsize := Spike.Lib.X64ConsumerA.updN (ls0T ls) l n)
    (fs := []) (lab := (Ly).lab) hJ
  exact Spike.Lib.X64.Flow.HelloWc.hello_wc_n4_segWA (p := helloSrc) (lbl := Spike.Lib.X64ConsumerA.upd (L0) l b)
    rfl hpS hendS hF hR (by show (-helloD : Int) ≤ -304; decide) (by show (8 : Int) ≤ 8; decide)
    (Spike.Lib.X64.HelloPh.MainWcL1Wj.hWp_L1PX hpw i0 E rd ls (I := IU) (m1 := m1) (σ1 := σ1) hp hpa hhp hlo0 hc
      hA13 hzL hl hslot)
    (Spike.Lib.X64.HelloPh.MainWcL1Wj.hWs_L1PX hpw i0 E rd ls (I := IU) (m1 := m1) (σ1 := σ1) hp hpa hhp hlo0 hc
      hA13 hzL hl hslot)
    hq hra
    (fun a ha m hm => Spike.Lib.X64.HelloPh.Level1I.hmem0_level1g hpw i0 E rd (IU) ls
      (own := fun s _ => Spike.Lib.X64.HelloPh.ownGHXW (Ly) (NT) s) hc l b n q hq a ha m hm.1)
    (Spike.Lib.X64.HelloPh.MainWcL1Q.hbox_L1 hJ)
    (fun q' h o' h1 h2 => let h' := hcell q' h o' h1 h2; ⟨h'.1, fun m hm => h'.2 m hm.1⟩)
    (Spike.Lib.X64.HelloPh.MainWcL1A.hxa_IUX hpw i0 E rd I ls hX hslot m1 σ1)

set_option hygiene false in
/-- Level 1's invariant at `I` at `OX` (`inv1G` of `W1Rg … OX` over `MS1X I`). -/
local notation "INV1X" => Spike.Lib.X64HelloPreA.H1Gfp.inv1G (W1Rg (asm := asm) hpw i0 E rd ls (OX)) (XR hpw i0)
  (TakeCKS (AX) (Spike.Lib.X64.HelloPh.ClH (Ly))) (L0) ((MS1X) I)

set_option maxHeartbeats 1600000 in
/-- **`hLandM1U_I` at `ownGHXW`** (module doc): `HLandM1U` at `inv1G (W1Rg … OX) … (MS1X I) ∧ U r1Of`:
`hlandM1_segX` at no frames, the heap abort closed (`Level1HAX.hello_hab_closedLAX` at `HabCtlA.habCtlHA_jr1L`),
carried from `invUH I` to `I` with `r1Of` unmapped (`KeepUnS.SegWS.mono_xa`, `keepUn`, the take by
`LandR1U.takeU_X`), in `inv1G` (`H1Gfp.inv1G_of_segWS`); the box call's `OKB` is carried from `HLandM1U`'s side (at
`ownGH`) field by field. Premises: the loader's facts, the certificate table's `z` (`hz`), and the box store's
landings at `MS1X I`'s `xa` (`hX`). -/
theorem hLandM1U_IX (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some SccCode.helloCells)
    (hlo0 : Λ0.code.lo = lo) (hc : Spike.Lib.X64.Rt.CtrZ o)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    (hz : i0 newTerm "z" 0 = some 0)
    (hX : ∀ l b n, (L0) l = none → AllocLand (AR).heap (AR).cells b n →
      Spike.Lib.X64.HelloPh.LandR1U.HLand2U (asm := asm) hpw i0 E rd ls l b n ((MS1X) I l b n []).xa) :
    ∀ l b n, (L0) l = none → AllocLand (AR).heap (AR).cells b n →
      HLandM1U (asm := asm) hpw i0 E rd ls l b n (fun s c fs => (INV1X) l b n s c fs ∧ U (R1) s) := by
  intro l b n hl hb fs ms0 R F q hms hG hok s c hAt htp hu
  obtain ⟨X, rfl⟩ : ∃ X, ms0 = { Spike.Lib.X64.HelloPh.Land.ref1H (asm := asm) hpw i0 E rd ls l b n fs with xa := X } :=
    ⟨_, hms⟩
  obtain ⟨rfl, hq, σC, m1, σ1, hslot, rfl, rfl, hra⟩ := hG
  refine ⟨?_, hu⟩
  have hqU : q.OKB ((MS1X) (IU) l b n []) (Ly).lab :=
    { hq with toS := { hq.toS with } }
  -- the allocator's tail to `wXA`, at no frames
  have hL := Spike.Lib.SegWS.liftS (W := fun s c fs => W1Rg (asm := asm) hpw i0 E rd ls (OX) l b n s c fs)
    (ms := (MS1X) (IU) l b n) [] (hlandM1_segX hpw i0 E rd I ls hpa hhp hlo0 hc hA13 hz hl (hX l b n hl hb) hslot m1 σ1
      hqU hra) fun _ _ h => h
  -- the heap abort closed
  have hC := Spike.Lib.X64.HelloPh.Level1HAX.hello_hab_closedLAX hpw i0
    (LB := Spike.Lib.X64ConsumerA.upd (L0) l b) (E := E) (rd := rd) (I := IU)
    (G := Spike.Lib.X64HelloGOf2H.gWH hpw IH (Spike.Lib.X64WakeHG.cTW hpw IH))
    (own := fun s _ => Spike.Lib.X64.HelloPh.ownGHXW (Ly) (NT) s) (ls := Spike.Lib.X64ConsumerA.updN (ls0T ls) l n)
    (Ctx := Spike.Lib.X64.HelloPh.Land.CtxR1H (asm := asm) hpw i0 E rd ls l b n)
    (ls0 := Spike.Lib.X64ConsumerA.updN (ls0T ls) l n) (frM := FR) (t := TV) (σC := σC)
    (Jr1 := Spike.Lib.X64.HelloPh.Land.Jr1LH hpw i0 l b) hpa hhp hlo0 hA13
    fun _ _ _ => Spike.Lib.X64.HelloPh.HabCtlA.habCtlHA_jr1L hpw i0 hl hslot hz rfl rfl rfl
      (show (-helloD : Int) ≤ -304 by decide) (show (0 : Int) ≤ 8 by decide)
  have h := Spike.Lib.X64.WakePh.Land5.segWS_mono_W
    (Spike.Lib.X64.WakePh.Land5.segWS_mono_K ((hL.mono_post (by
        rintro s c fs ⟨h, hfs⟩; exact ⟨⟨_, m1, σ1, h⟩, hfs⟩)).seq hC)
      fun s c fs hW s' => Spike.Lib.X64.HelloPh.StartH0B.takeCKS_iffH hpw IH hW.2.1)
    (W' := fun s c fs => W1Rg (asm := asm) hpw i0 E rd ls (OX) l b n s c fs ∧ XR hpw i0 l b n s c fs)
    fun s c fs h => ⟨h, h.2.1⟩
  -- from `invUH I` to `I`, `r1Of` unmapped
  have hXU := Spike.Lib.X64.KeepUnS.SegWS.mono_xa (ms' := fun fs => unXa ((MS1X) I l b n fs) (R1)) h
    (fun _ => rfl) fun _ _ _ _ _ _ hx hu => ⟨hx.1, hx.2 hu⟩
  have hU := Spike.Lib.X64.KeepUnS.SegWS.keepUn (fun _ => rfl) hXU
    fun s _ _ hW s' hk hu => Spike.Lib.X64.HelloPh.LandR1U.takeU_X hpw i0 s s' hW.2 hk hu
  exact Spike.Lib.X64HelloPreA.H1Gfp.inv1G_of_segWS (hU.mono_post fun _ _ _ h => h.1) s c [] ⟨⟨⟨hAt, htp⟩, rfl⟩, hu⟩

end Spike.Lib.X64.HelloPh.LandM1U

/-- info: 'Spike.Lib.X64.HelloPh.LandM1U.HLandM1U.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.LandM1U.HLandM1U.mono

/-- info: 'Spike.Lib.X64.HelloPh.LandM1U.inv1_I3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.LandM1U.inv1_I3

/-- info: 'Spike.Lib.X64.HelloPh.LandM1U.hlandM1_segX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.LandM1U.hlandM1_segX

/-- info: 'Spike.Lib.X64.HelloPh.LandM1U.hLandM1U_IX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.LandM1U.hLandM1U_IX
