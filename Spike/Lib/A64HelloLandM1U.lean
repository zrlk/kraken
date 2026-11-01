/-
**The root's `hM`: `wc_main`'s box counter add's tail at level 1, in level 1's invariant** (AArch64, row H2-U-hM;
the level-1 twin of `Spike/Lib/A64HelloLandRd.lean`'s `hlandRd_U`, as wake's `Spike/Lib/A64WakeLand4.lean`
`hland_R`): `LandR1U.HLandM1U` at `inv1G W1R XR … (MS1 I) ∧ U r1Of`, `RootL1U.hW1_rootU`'s `hM`.

From the allocator's `n4` after the counter add of `wc_main`'s box call (`Land.GcM1H`: the first stack's top, the
caller's slot `-80` main's TCB, `wc_main`'s entry at `Level1I`'s `JrRL` and its caller's at `Jr1LH l b`):
- the allocator's rest, its exits resumed in `wc_main`'s frame, then `.sp0`, to the heap abort at `wXA`
  (`HelloWc.hello_wc_n4_segWA`), at the level's memory sides at `invUH I` (`I` asked only with `r1Of` unmapped), with
  `wc_main`'s `hWp`/`hWs` (`MainWcL1Wj.hWp_L1P`/`hWs_L1P`), the box's words and cell (`Level1M.hmem0_level1`,
  `MainWcL1Q.hbox_L1`/`hcell0_L1`) and its landing (`MainWcL1A.hxa_IU`, from `HLand2U` at `I`'s `xa`);
- the heap abort closed (`Level1HA.hello_hab_closedLA`, its controls `HabCtlA.habCtlHA_jr1L`);
- carried to the level's memory sides at `I` with `r1Of` unmapped (`KeepUnS.SegWS.mono_xa`/`keepUn`, as
  `Level1IU.hB_landU`), so its start is in `inv1G` (`H1Gfp.inv1G_of_segWS`). `U r1Of` is `HLandM1U`'s own premise.

The landing is `I`'s, not `IH D`'s: at the root `I := RootL1F.I0H …` (`inv0H` and `inv1G` depend on `IH D`).

- `hlandM1_seg`: the allocator's tail from `n4` to `wXA` at `invUH I`.
- `hLandM1U_I`: `HLandM1U` at `inv1G … (MS1 I) ∧ U r1Of`.
- `HLandM1U.mono`, `inv1_I3`: the plug into the root's `IH D` (`I3`'s level-1 disjunct).
-/
import Spike.Lib.A64HelloWcN4A
import Spike.Lib.A64HelloMainWcL1A
import Spike.Lib.A64HelloLevel1IU
import Spike.Lib.A64HelloH1Gfp

namespace Spike.Lib.A64.HelloPh.LandM1U

variable {asm : String}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Entry)
open Scc.Sem.A64 (abi textProgram)
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64ConsumerA (TakeCKS)
open Spike.Lib.A64.WakePh (lo)
open Spike.Lib (FragS Frag MemSide SegWS SegW)
open Spike.Lib.A64.Flow (swR At)
open Spike.Lib.A64.Flow.Ret0 (CallerCells)
open Spike.Lib.A64.Flow.Hello1 (mWC)
open Spike.Lib.A64.Flow.HelloM (wcJ0 wcR wcF JrT)
open Spike.Lib.A64.Flow.HelloWc (wARH WcCtxH wXA)
open Spike.Lib.A64.Flow.HelloJr1 (JrRL)
open Spike.Lib.A64.WakePh.MainGlue (FS)
open Spike.Lib.A64.KeepTP (TP)
open Spike.Lib.A64.KeepUn (U unXa)
open Spike.Lib.A64.Alloc (Call)
open Spike.Lib.A64.HelloPh.StartGlue (X0WH)
open Spike.Lib.A64.HelloPh.StartH0G (helloD helloLsw)
open Spike.Lib.A64.HelloPh.StartH0U (invUH)
open Spike.Lib.A64.HelloPh.Level1I (W1R XR)
open Spike.Lib.A64.HelloPh.LandR1U (HLandM1U)
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.WakeLoadT (L0T ls0T)
open Spike.Lib.A64.HelloPh.C0S (c0S)
open Spike.Lib.HelloSrc (helloSrc)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.A64.Flow.AS

/-! ## `HLandM1U` is monotone; `I3`'s level-1 disjunct -/

/-- **`HLandM1U` is monotone in its target.** -/
theorem HLandM1U.mono {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
    {hpw : PlaceW pcfg Λ0 o} {i0 : CoreTerm.Expr → String → Nat → Option Nat} {E : Entry}
    {rd : TermRun.Word → Prop} {ls : Lsize} {l : WeakMem.AllocLabel} {b n : Nat} {Q Q' : FragS isaLSE2}
    (h : HLandM1U (asm := asm) hpw i0 E rd ls l b n Q) (hQ : ∀ s c fs, Q s c fs → Q' s c fs) :
    HLandM1U (asm := asm) hpw i0 E rd ls l b n Q' :=
  fun fs ms0 R F q hms hG hok s c hAt htp hu => hQ s c fs (h fs ms0 R F q hms hG hok s c hAt htp hu)

/-- **Level 1's invariant is in `I3` at the level's labels** (`I3`'s second disjunct, the root's `IH D` at
`upd L0 l b`, `updN ls0 l n`). -/
theorem inv1_I3 {ar : Spike.Lib.Arena} {L0 : Lbl} {ls0 : Lsize} {inv0 : FragS isaLSE2}
    {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    {inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    {l : WeakMem.AllocLabel} {b n : Nat} (hl : L0 l = none) (hb : AllocLand ar.heap ar.cells b n) :
    ∀ s c fs, inv1 l b n s c fs →
      Spike.Lib.A64ConsumerA.I3 ar L0 ls0 inv0 inv1 inv2 (Spike.Lib.A64ConsumerA.upd L0 l b)
        (Spike.Lib.A64ConsumerA.updN ls0 l n) s c fs :=
  fun _ _ _ h => .inr (.inl ⟨l, b, n, hl, hb, rfl, rfl, h⟩)

/-! ## The allocator's tail -/

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (rd : TermRun.Word → Prop) (I : Spike.Lib.A64ConsumerS.InvS) (ls : Lsize)

set_option hygiene false in
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
local notation "FR" => Spike.Lib.HelloRdCf.frH c0S.env

set_option hygiene false in
local notation "KR" => Spike.Lib.A64.PhRec.K (Ly) RS

set_option hygiene false in
/-- The child's stack. -/
local notation "R1" => Spike.Lib.A64.Rt.PreChild.r1Of (Ly).lab

set_option hygiene false in
/-- main's thread pointer. -/
local notation "TV" => UInt64.ofBitVec (Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64)

set_option hygiene false in
/-- The first stack's top (the start's `v`). -/
local notation "TOP" => Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64

set_option hygiene false in
/-- The fragment `I` asked only with `r1Of` unmapped. -/
local notation "IU" => invUH hpw i0 I

set_option hygiene false in
/-- The level's memory sides at a fragment `J` after rodata's allocation of `l` at `b`, `n` words, at `fs`. -/
local notation "MS1" => fun (J : Spike.Lib.A64ConsumerS.InvS) (l : WeakMem.AllocLabel) (b n : Nat)
    (fs : List TermRun.Frame) =>
  Spike.Lib.A64ConsumerA.msOfA (Ly).Λ
    ((Scc.Sem.A64.target (Scc.Sem.A64.kernel 2) E).marks asm (Ly).Λ) rd
    (Spike.Lib.HelloGOf2H.gWH hpw IH (Spike.Lib.WakeHG.cTW hpw IH))
    (fun s _ => Spike.Lib.A64.HelloPh.ownGH (Ly) NT s)
    (AR) J (Spike.Lib.A64ConsumerA.upd (LB) l b) (Spike.Lib.A64ConsumerA.updN (ls0T ls) l n) fs

set_option hygiene false in
/-- `wc_main`'s region at the call. -/
local notation "RW" => wcR (swR (TOP) (-helloLsw) 0) helloD

set_option hygiene false in
/-- `wc_main`'s frame condition at the caller's state `m1`, `σ1`. -/
local notation "FW" => wcF (swR (TOP) (-helloLsw) 0) helloD (FS (Ly) (RS) helloLsw 0#64 (TOP)) m1 σ1

set_option hygiene false in
/-- `wc_main`'s entry invariant at `Level1I`'s `Jr` (`Land.GcM1H`'s). -/
local notation "J0" => wcJ0 (mWC (Ly).lab σC (JrT (JrRL (Spike.Lib.A64ConsumerA.upd (LB) l b) c0S.env l) (TV)
  (swR (TOP) (-helloLsw) 0))).J σ1

set_option hygiene false in
/-- `wc_main`'s caller's invariant at the box's `new` (`Land.Jr1LH`). -/
local notation "J1" => wcJ0 (mWC (Ly).lab σC (Spike.Lib.A64.HelloPh.Land.Jr1LH hpw i0 l b)).J σ1

set_option maxHeartbeats 1600000 in
/-- **The allocator's tail from `n4` at `invUH I`** (module doc): from the allocator's `n4` of `wc_main`'s box call
at the pinned caller (the slot `-80` main's TCB, `hslot`) under main's thread pointer, a segment inside the level
`W1R` at no frames to the heap abort at `wXA`, at the level's memory sides at `invUH I`. -/
theorem hlandM1_seg (hpa : textProgram asm = .ok o.prog)
    (hhp : textProgram asm = .ok SccCode.helloProg)
    (hlo0 : Λ0.code.lo = lo) (hc : Spike.Lib.A64.Rt.CtrZ o)
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    (hz : i0 Spike.Lib.HelloMainPreSrc.newTerm "z" 0 = some 0)
    {l : WeakMem.AllocLabel} {b n : Nat} (hl : (LB) l = none)
    (hX : Spike.Lib.A64.HelloPh.LandR1U.HLand2U (asm := asm) hpw i0 E rd ls l b n ((MS1) I l b n []).xa)
    {σC : FAS} (hslot : σC.slot (-80) = Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64)
    (m1 : MachineData) (σ1 : FAS) {q : Call} (hq : q.OKB ((MS1) (IU) l b n []) (Ly).lab)
    (hra : q.ra = ((Ly).lab ".L22_wc_main.sp0").toBitVec) :
    SegW (fun s c => W1R (asm := asm) hpw i0 E rd ls l b n s c []) (KR) helloSrc
      (Spike.Lib.A64ConsumerA.upd (LB) l b) ((MS1) (IU) l b n [])
      (fun s c => At (Ly).exe (Ly).endPc (wARH (RW)) (fun m => (FW) m ∧ CallerCells (RW) (-144) (-160) 0 m ∧
          WcCtxH ((MS1) (IU) l b n []) (Ly).lab (RW) (J0) (J1) q m)
        (Spike.Lib.A64.Alloc.N (Ly).lab ((MS1) (IU) l b n []) q .n4) s c ∧ TP (TV) s)
      (fun s c => At (Ly).exe (Ly).endPc (RW) (FW) (wXA ((MS1) (IU) l b n []) (Ly).lab (J1)) s c ∧ TP (TV) s) := by
  have hp : o.prog = SccCode.helloProg := Except.ok.inj (hpa.symm.trans hhp)
  have hprog : (Ly).prog = SccCode.helloProg := hp
  have hpS : Lays (Ly).exe SccCode.helloProg (Ly).pfx := hprog ▸ (Ly).lays
  have hendS : (Ly).endPc = endOf (Ly).exe SccCode.helloProg (Ly).pfx := by
    show endOf (Ly).exe (Ly).prog (Ly).pfx = _; rw [hprog]
  have : Kraken.Executable.ValidLayout (Ly).exe := (Ly).valid
  obtain ⟨hok, hal0, hF0⟩ := Spike.Lib.A64.HelloPh.Land.fstable_FS hpw i0
  obtain ⟨hR, hal, hF⟩ := Spike.Lib.A64.Flow.HelloM.wcR_ok (D := helloD) (by decide) (by decide) hok hal0 hF0
    (by show (-helloLsw : Int) ≤ -80 - helloD; decide) (by show (0 : Int) ≤ 0; decide) m1 σ1
  have hzL := Spike.Lib.A64.HelloPh.MainWcL1A.hzL hpw i0 hz
  have hcell := Spike.Lib.A64.HelloPh.MainWcL1Q.hcell0_L1 hpw IH
    (μ := (Scc.Sem.A64.target (Scc.Sem.A64.kernel 2) E).marks asm (Ly).Λ) (rd := rd)
    (own := fun s _ => Spike.Lib.A64.HelloPh.ownGH (Ly) NT s) (I := IU)
    (lbl := Spike.Lib.A64ConsumerA.upd (LB) l b) (lsize := Spike.Lib.A64ConsumerA.updN (ls0T ls) l n)
    (fs := []) (lab := (Ly).lab)
    (Spike.Lib.A64.HelloPh.MainWcL1Wp.hJ_L1 hpw i0 (l := l) (b := b) (σC := σC) (σ1 := σ1))
  exact Spike.Lib.A64.Flow.HelloWc.hello_wc_n4_segWA (p := helloSrc) (lbl := Spike.Lib.A64ConsumerA.upd (LB) l b)
    rfl hpS hendS hF hR hal (by show (-helloD : Int) ≤ -304; decide) (by show (0 : Int) ≤ 0; decide)
    (Spike.Lib.A64.HelloPh.MainWcL1Wj.hWp_L1P hpw i0 E rd ls (I := IU) (m1 := m1) (σ1 := σ1) hp hlo0 hc hA13 hzL
      hl hslot)
    (Spike.Lib.A64.HelloPh.MainWcL1Wj.hWs_L1P hpw i0 E rd ls (I := IU) (m1 := m1) (σ1 := σ1) hp hlo0 hc hA13 hzL
      hl hslot)
    hq hra
    (fun a ha m hm => Spike.Lib.A64.HelloPh.Level1I.hmem0_level1 hpw i0 E rd (IU) ls hc l b n q hq a ha m hm.1)
    (Spike.Lib.A64.HelloPh.MainWcL1Q.hbox_L1 (Spike.Lib.A64.HelloPh.MainWcL1Wp.hJ_L1 hpw i0 (l := l) (b := b) (σC := σC)
      (σ1 := σ1)))
    (fun q' h o' h1 h2 => let h' := hcell q' h o' h1 h2; ⟨h'.1, fun m hm => h'.2 m hm.1⟩)
    (Spike.Lib.A64.HelloPh.MainWcL1A.hxa_IU hpw i0 E rd I ls hX hslot m1 σ1)

set_option hygiene false in
/-- Level 1's invariant at `I` (`inv1G` over the level's memory sides at `I`). -/
local notation "INV1" => Spike.Lib.HelloPreA.H1Gfp.inv1G (W1R (asm := asm) hpw i0 E rd ls) (XR hpw i0)
  (TakeCKS (AX) (Spike.Lib.A64.HelloPh.ClH (Ly))) (LB) ((MS1) I)

set_option maxHeartbeats 1600000 in
/-- **`HLandM1U` at level 1's invariant** (module doc): `hlandM1_seg` at no frames, the heap abort closed
(`Level1HA.hello_hab_closedLA` at `HabCtlA.habCtlHA_jr1L`), carried from `invUH I` to `I` with `r1Of` unmapped
(`KeepUnS.SegWS.mono_xa`, `keepUn`, the take by `LandR1U.takeU_X`), in `inv1G` (`H1Gfp.inv1G_of_segWS`); `U r1Of`
is `HLandM1U`'s premise. Premises: the loader's facts, the certificate table's `z` (`hz`; at the root
`HabCtlA.hz_i0M`), and the box store's landings at `I`'s `xa` (`hX`; at the root `RootHP.hland2_boxMRU`). -/
theorem hLandM1U_I (hpa : textProgram asm = .ok o.prog)
    (hhp : textProgram asm = .ok SccCode.helloProg)
    (hlo0 : Λ0.code.lo = lo) (hc : Spike.Lib.A64.Rt.CtrZ o)
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    (hz : i0 Spike.Lib.HelloMainPreSrc.newTerm "z" 0 = some 0)
    (hX : ∀ l b n, (LB) l = none → AllocLand (AR).heap (AR).cells b n →
      Spike.Lib.A64.HelloPh.LandR1U.HLand2U (asm := asm) hpw i0 E rd ls l b n ((MS1) I l b n []).xa) :
    ∀ l b n, (LB) l = none → AllocLand (AR).heap (AR).cells b n →
      HLandM1U (asm := asm) hpw i0 E rd ls l b n (fun s c fs => (INV1) l b n s c fs ∧ U (R1) s) := by
  intro l b n hl hb fs ms0 R F q hms hG hok s c hAt htp hu
  obtain ⟨X, rfl⟩ : ∃ X, ms0 = { Spike.Lib.A64.HelloPh.Land.ref1H (asm := asm) hpw i0 E rd ls l b n fs with xa := X } :=
    ⟨_, hms⟩
  obtain ⟨rfl, hq, σC, m1, σ1, hslot, rfl, rfl, hra⟩ := hG
  refine ⟨?_, hu⟩
  have hqU : q.OKB ((MS1) (IU) l b n []) (Ly).lab := Spike.Lib.A64.HelloPh.Level1IU.okb_xa rfl hq
  -- the allocator's tail to `wXA`, at no frames
  have hL := Spike.Lib.SegWS.liftS (W := fun s c fs => W1R (asm := asm) hpw i0 E rd ls l b n s c fs)
    (ms := (MS1) (IU) l b n) [] (hlandM1_seg hpw i0 E rd I ls hpa hhp hlo0 hc hA13 hz hl (hX l b n hl hb) hslot m1 σ1
      hqU hra) fun _ _ h => h
  -- the heap abort closed
  have hC := Spike.Lib.A64.HelloPh.Level1HA.hello_hab_closedLA hpw IH (E := E) (rd := rd) (I := IU)
    (G := Spike.Lib.HelloGOf2H.gWH hpw IH (Spike.Lib.WakeHG.cTW hpw IH))
    (own := fun s _ => Spike.Lib.A64.HelloPh.ownGH (Ly) NT s) (ls := Spike.Lib.A64ConsumerA.updN (ls0T ls) l n)
    (Ctx := Spike.Lib.A64.HelloPh.Land.CtxR1H (asm := asm) hpw i0 E rd ls l b n)
    (ls0 := Spike.Lib.A64ConsumerA.updN (ls0T ls) l n) (frM := FR) (t := TV) (m0 := m1) (σC := σC)
    (Jr1 := Spike.Lib.A64.HelloPh.Land.Jr1LH hpw i0 l b) hpa hhp hlo0
    fun _ _ _ => Spike.Lib.A64.HelloPh.HabCtlA.habCtlHA_jr1L hpw i0 hl hslot hz rfl rfl rfl
      (show (-helloD : Int) ≤ -304 by decide) (show (0 : Int) ≤ 0 by decide)
  have h := ((((hL.mono_post fun s c fs ⟨h, hfs⟩ => ⟨⟨_, m1, σ1, h⟩, hfs⟩).seq hC).mono_K
      fun s c fs hW s' => Spike.Lib.A64.HelloPh.StartH0B.takeCKS_iffH hpw IH hW.2.1).mono_W
    (W' := fun s c fs => W1R (asm := asm) hpw i0 E rd ls l b n s c fs ∧ XR hpw i0 l b n s c fs)
    fun s c fs h => ⟨h, h.2.1⟩)
  -- from `invUH I` to `I`, `r1Of` unmapped
  have hXU := Spike.Lib.A64.KeepUnS.SegWS.mono_xa (ms' := fun fs => unXa ((MS1) I l b n fs) (R1)) h
    (fun _ => rfl) fun _ _ _ _ _ _ hx hu => ⟨hx.1, hx.2 hu⟩
  have hU := Spike.Lib.A64.KeepUnS.SegWS.keepUn (fun _ => rfl) hXU
    fun s _ _ hW s' hk hu => Spike.Lib.A64.HelloPh.LandR1U.takeU_X hpw i0 hA13 s s' hW.2 hk hu
  exact Spike.Lib.HelloPreA.H1Gfp.inv1G_of_segWS (hU.mono_post fun _ _ _ h => h.1) s c [] ⟨⟨⟨hAt, htp⟩, rfl⟩, hu⟩

end Spike.Lib.A64.HelloPh.LandM1U

/-- info: 'Spike.Lib.A64.HelloPh.LandM1U.HLandM1U.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.LandM1U.HLandM1U.mono

/-- info: 'Spike.Lib.A64.HelloPh.LandM1U.inv1_I3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.LandM1U.inv1_I3

/-- info: 'Spike.Lib.A64.HelloPh.LandM1U.hlandM1_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.LandM1U.hlandM1_seg

/-- info: 'Spike.Lib.A64.HelloPh.LandM1U.hLandM1U_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.LandM1U.hLandM1U_I
