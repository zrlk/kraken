/-
**`wake_start_wc_h0`'s `hxa` from `h1`'s `Box` clause** (wake.w, x86-64):
at the start control `c0W`, the box's landing past its store (`bX` on
`(wR (RS wcLsw v) wcD).fp (-8)`, `wc_main`'s frame condition `wF … FS …`)
under main's thread pointer is a `Box`, so `h1`'s `Box ⊆ inv1` clause puts
it in `inv1`, and the landing is in the memory side's allocation fragment
(`AllocLand` from `bX`'s allocator fact, `I2`'s `inv1` disjunct).

- `wJ0_c0W`: `wc_main`'s entry invariant at `JS … c0` pins the source at
  `c0` and `%rdi` at the first TCB's thread pointer.
- `load_of_off`: a stack range's words load, off a region by `StackOff`,
  inside it by `Abs`.
- `fp_geom`: `hxa`'s region `(wR (RS wcLsw v) wcD).fp (-8)` is a region,
  based at `v - 64`, offsets `[-320, 16)`.
- `box_landing`: the landing is a `Box`, given the child's stack unmapped
  (`KeepUn.U`, `hu`) and `wc_main`'s frame condition inside `F0` (`hF0`).
- `hxa_R`: `hxa` at `msOfA … (arW hpw i) (I2 (arW hpw i) L0 ls0 inv0 inv1)`,
  given `h1`'s `Box` clause (`hB1`), `hF0` and the open `hUn1`.

x86-64 twin of `Spike/Lib/A64WakeHxa.lean` (namespace
`Spike.Lib.X64.WakePh.Hxa`, same names, plus `fp_geom`).

**Where x86-64 differs from AArch64**:
- the layout is `RuntimeLayout.ofPlaceWX hpw i` (A64 `ofPlaceW hp IW`);
  `wc_main`'s region is `wR (RS wcLsw v) wcD` at `wcD = 328`, `wcLsw = 384`
  (A64 `wR (swR v (-384) 0) 336`), and the landing is on its `fp (-8)` (the
  frame based at the saved `%rbp`), so `Box`'s region is that re-based
  region (`fp_geom`; `FStable.fp` of `WakeM.wR_ok`'s frame condition);
- the thread pointer is `tpOf (tcbS Ly)` and the TCB argument `%rdi` (A64
  `x0`); `Box`'s second-stack-top fact is `base + 64 = stacksA + 16384`;
- `Box` has no "words at `0`, `8` above the region" clause (A64's first
  bullet), its main stack off the region is `StackOff` at the re-based
  region (`StartPlaceLy.stackOff_r0_boxFp`);
- the memory side is generic over the caller's fragment: `hxa_R` is stated
  at `msOfA` with `I2 (arW hpw i) L0 ls0 inv0 inv1` (A64 at `msBot E []`
  with `WakeRoot.H1R`), and takes `h1`'s `Box ⊆ inv1` clause (`hB1`,
  `fun l b n hl hb => (h1 l b n hl hb).2.1` from an `H1Stmt`) rather than the
  whole statement;
- `box_landing` is generic in the memory side `ms0` (it reads only the
  box call's `OKB.term`/`ev`);
- the arena's units and offset are proved here (`units_off`, as
  `StartH0`'s private one; A64 `LowerA64.arOf_units_pos`/`arOf_off_eq`).
-/
import Spike.Lib.X64WakeStartPlaceXT
import Spike.Lib.X64WakeTakeFLy
import Spike.Lib.X64WakeC0
import Spike.Lib.X64WakeBoxW
import Spike.Lib.X64WakeOD
import Spike.Lib.X64AtRebase
import Spike.Lib.X64WakeWcWfR
import Spike.Lib.X64SegInstA

namespace Spike.Lib.X64.WakePh.Hxa

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64.WakePh.MainGlue (FS JS RS tcbS topS)
open Spike.Lib.X64.WakePh.StartFacts (wcD wcLsw)
open Spike.Lib.X64 (swR At)
open Spike.Lib.X64.Flow.Ret0 (tpOf)
open Spike.Lib.X64.Flow.WakeM (wR wF wJ0 wNC)
open Spike.Lib.X64.Flow.WakeWc (bX)
open Spike.Lib.X64.KeepTP (TP)
open Spike.Lib (FragS MemSide Region PlaceWX)
open Spike.Lib.X64.WakeC0 (c0W)

/-- **`wc_main`'s entry invariant at `JS … c0`**: the source at `c0`,
`%rdi` the first TCB's thread pointer. -/
theorem wJ0_c0W {L : RuntimeLayout} {k0 : BitVec 64} {c0 : Ctl} {σC σ : Spike.Lib.X64.AS} {c : Ctl}
    (h : wJ0 (wNC L.lab (JS L k0 c0)).J σC σ c) :
    c = c0 ∧ σ.regs.rdi.toBitVec = (tpOf (tcbS L)).toBitVec := by
  obtain ⟨rfl, ⟨σe, ⟨⟨hc, -, -⟩, hrdi⟩, -, -, h16, -, -⟩, hrdiC, -, -⟩ := h
  refine ⟨hc, ?_⟩
  show σC.regs.rdi.toBitVec = _
  rw [hrdiC, h16, hrdi]

/-- **A stack range's words load** when those off a region load
(`StackOff`) and the region's cells are an abstraction's (`Abs`), the
region's base and bounds word-aligned. -/
theorem load_of_off {R : Region} {rS : Scc.Sem.Range} {o : Spike.Lib.X64.SO} {m : MachineData}
    {σ : Spike.Lib.X64.AS} (hR : R.OK) (hal : R.base.toNat % 8 = 0) (hlo8 : R.lo % 8 = 0)
    (hhi8 : R.hi % 8 = 0) (hSO : Spike.Lib.X64.Flow.Ret0.StackOff rS R m) (hA : Spike.Lib.X64.Abs R o m σ) :
    ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) → (Mem.loadInt m.dmem (BitVec.ofNat 64 a) 8).isSome := by
  intro a h8 ha ha7
  by_cases hout : (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a
  · exact hSO a h8 ha ha7 hout
  · have hk : R.Off ((a : Int) - R.base.toNat) := ⟨by omega, by omega, by omega⟩
    have he := R.addr_toNat hR hk
    have hlt := (R.addr ((a : Int) - R.base.toNat)).isLt
    obtain ⟨j, hj, -⟩ := hA.slot _ hk
    have ea : BitVec.ofNat 64 a = R.addr ((a : Int) - R.base.toNat) := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; omega
    rw [ea, hj]; rfl

set_option linter.unusedSimpArgs false in
/-- **`hxa`'s region** `(wR (RS wcLsw v) wcD).fp (-8)` at a high enough
switch base `v`: a region, based at `v - 64`, offsets `[-320, 16)`. -/
theorem fp_geom {v : BitVec 64} (hv : 384 ≤ v.toNat) :
    ((wR (RS wcLsw v) wcD).fp (-8)).OK ∧
      (((wR (RS wcLsw v) wcD).fp (-8)).base.toNat : Int) = v.toNat + -64 ∧
      ((wR (RS wcLsw v) wcD).fp (-8)).lo = -320 ∧ ((wR (RS wcLsw v) wcD).fp (-8)).hi = 16 := by
  rw [StartFacts.wcD_eq.1, StartFacts.wcD_eq.2]
  obtain ⟨hR, hb⟩ := Spike.Lib.X64.WakePh.StartPlaceLy.rs_ok (v := v) hv
  have hRw : (wR (RS 384 v) 328).OK :=
    Spike.Lib.Region.callee_ok hR (by simp [Spike.Lib.Region.callee, Spike.Lib.X64.swR])
      (by simp [Spike.Lib.Region.callee, Spike.Lib.X64.swR]) (by simp [Spike.Lib.Region.callee, Spike.Lib.X64.swR])
      (by simp [Spike.Lib.Region.callee, Spike.Lib.X64.swR])
  have hbw := Spike.Lib.Region.callee_base (hi' := 8) hR (kc := -48) (lo' := -328)
    (by simp [Spike.Lib.Region.callee, Spike.Lib.X64.swR]) (by simp [Spike.Lib.Region.callee, Spike.Lib.X64.swR])
    (by simp [Spike.Lib.Region.callee, Spike.Lib.X64.swR])
  have hb' : ((wR (RS 384 v) 328).base.toNat : Int) = v.toNat + -56 := by
    rw [show wR (RS 384 v) 328 = (RS 384 v).callee (-48) (-328) 8 from rfl, hbw, hb]
    omega
  have h1 : (wR (RS 384 v) 328).lo ≤ -8 := by show (-328 : Int) ≤ -8; decide
  have h2 : (-8 : Int) < (wR (RS 384 v) 328).hi := by show (-8 : Int) < 8; decide
  refine ⟨Spike.Lib.Region.fp_ok hRw h1 h2, ?_, rfl, rfl⟩
  rw [Spike.Lib.Region.fp_base hRw h1 h2, hb']
  omega

/-- The arena's units of a type with accesses are positive, its offset one
header word (as `StartH0`'s private `units_off`). -/
private theorem units_off {Λ : Scc.Sem.Layout} {τ : Ty}
    (hacc : ∃ us, TermRun.accs (TermRun.close [] τ) = some us) :
    1 ≤ (Spike.Lib.X64.Rt.arOf Λ).units 1 τ ∧ (Spike.Lib.X64.Rt.arOf Λ).off 1 τ = 8 := by
  obtain ⟨us, hus⟩ := hacc
  refine ⟨?_, ?_⟩
  · simp only [Spike.Lib.X64.Rt.arOf, Arena.ofWords, hus]
    split <;> omega
  · simp only [Spike.Lib.X64.Rt.arOf, Arena.ofWords, hus, Nat.mul_zero]

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw i

set_option hygiene false in
local notation "RS0" => Spike.Lib.X64.Rt.rS0 (Ly)

set_option hygiene false in
local notation "AR" => Spike.Lib.X64.WakeOD.arW hpw i

set_option hygiene false in
local notation "JW" => fun σC => wJ0 (wNC (Ly).lab (JS (Ly) 0#64 c0W)).J σC

set_option hygiene false in
local notation "TPW" => TP (tpOf (tcbS (Ly)))

set_option hygiene false in
local notation "R1" => Spike.Lib.X64.Rt.PreChild.r1Of (Ly).lab

set_option hygiene false in
/-- The memory side of `wake_start_wc_h0` at wake's arena and the one-box
fragment `I2`. -/
local notation "MS" => Spike.Lib.X64ConsumerA.msOfA (Ly).Λ μ rd (Spike.Lib.X64WakeOG.gW hpw i cT)
  (fun s _ => Spike.Lib.X64.WakePh.ownGXW (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab) s) (AR)
  (Spike.Lib.X64ConsumerA.I2 (AR) L0 ls0 inv0 inv1) L0 ls0 []

set_option linter.unusedSimpArgs false in
/-- **The box's landing is a `Box`** at any memory side `ms0`: `wc_main`'s
region `wR (RS wcLsw v) wcD` re-based at `-8`, its frame condition
`wF … FS …`, the entry node at `JS … c0W`, the thread pointer the first
TCB's; the source at `c0W` past its `new`; main's stack owned (`StackOff`
off the region, `Abs` inside), the child's stack unmapped (`hu`). -/
theorem box_landing (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    {ms0 : MemSide isa} {F0 : MachineData → Prop}
    (hF0 : ∀ v m0 σC m, wF (RS wcLsw v) wcD (FS (Ly) RS0 wcLsw 0#64 v) m0 σC m → F0 m)
    {v : BitVec 64} {m0 : MachineData} {σC : Spike.Lib.X64.AS} {l : WeakMem.AllocLabel} {A : Nat}
    {s : State} {c : Ctl}
    (hA : At (Ly).exe (Ly).endPc ((wR (RS wcLsw v) wcD).fp (-8)) (wF (RS wcLsw v) wcD (FS (Ly) RS0 wcLsw 0#64 v) m0 σC)
      (bX ms0 (Ly).lab ((JW) σC) l A) s c)
    (htp : TPW s) (hu : Spike.Lib.X64.KeepUn.U R1 s) :
    Spike.Lib.X64.Flow.WakeWc.Box (Ly) ms0 F0 l A 1 s c := by
  have hA0 := hA
  obtain ⟨-, -, -, -, σ, hAbs, hFm, hJ⟩ := hA
  have hv := Spike.Lib.X64.WakePh.WcWfR.v_top hFm
  subst hv
  -- the first stack's top and `wc_main`'s region there
  have hst := (Ly).stacks_sub
  have hsal := (Ly).stacks_al
  have hpf := (Ly).pool_fit
  simp only [Scc.Sem.Range.Sub] at hst
  have hT := Spike.Lib.X64.WakePh.StartPlaceLy.v_top hpw i (v := topS (Ly) 0#64) rfl
  have hwf := Spike.Lib.PlaceWX.wf_link_of_placeWX i hpw
  have hsub := Spike.Lib.X64.Rt.rS0_sub (Ly)
  have hok : (Spike.Lib.X64.swR (topS (Ly) 0#64) (-wcLsw) 0).OK := by
    (try simp only [topS, tcbS]); rw [Spike.Lib.X64.Rt.stacksA_lab0]
    exact Spike.Lib.X64.Rt.rt_hokD _ (by decide) (by decide)
  have hFwS := Spike.Lib.X64.Rt.wordsNoneP_swFSL_fstable
    (a := Spike.Lib.X64.Flow.Ret0.limA (tpOf (tcbS (Ly)))) (v := topS (Ly) 0#64) hwf hsub hok (by decide)
    (by decide)
    (by (try simp only [topS, tcbS]); rw [Spike.Lib.X64.Rt.stacksA_lab0]
        exact Spike.Lib.X64.Rt.rS0_subRD _ (by decide) (by decide))
    (by (try simp only [topS, tcbS]); rw [Spike.Lib.X64.Rt.pinA_lab0]; exact Spike.Lib.X64.Rt.rt_hfit _)
    (by (try simp only [topS, tcbS]); rw [Spike.Lib.X64.Rt.pinA_lab0, Spike.Lib.X64.Rt.stacksA_lab0]
        exact Spike.Lib.X64.Rt.rt_houtD _ (by decide) (by decide))
    (Spike.Lib.X64.Rt.fitS_of_sub _ hsub)
  have hR2 := Spike.Lib.X64.Rt.mainEF_ok (tcb := tcbS (Ly)) (by decide) (by decide) hok hFwS
  obtain ⟨hRw, hFw⟩ := Spike.Lib.X64.Flow.WakeM.wR_ok (D := wcD) (by decide) (by decide) hR2.1 hR2.2
    (by show (8 : Int) - wcLsw ≤ -48 - wcD; decide) (by show (0 : Int) ≤ 8; decide) m0 σC
  have hRF := Spike.Lib.X64.FStable.fp hRw (d := -8) (by show -wcD ≤ (-8 : Int); decide)
    (by show (-8 : Int) < 8; decide) hFw
  obtain ⟨hRok, hb, hRlo, hRhi⟩ := fp_geom (v := topS (Ly) 0#64) (by omega)
  have hSO := Spike.Lib.X64.WakePh.StartPlaceLy.stackOff_r0_boxFp hpw i _ hFm
  have hr0 : (Spike.Lib.X64.Rt.Ti2.r0Of (Ly).lab).lo = (Ly).stacksA.toNat := by
    show (Spike.Lib.X64.Flow.Ret0.stacksA (_root_.Executable.labels (Ly).exe).label + 0#64).toNat = _
    rw [(Ly).lab_stacks, BitVec.add_zero]
  have hr0s : (Spike.Lib.X64.Rt.Ti2.r0Of (Ly).lab).size = 16384 := rfl
  -- the source at `c0W` past its `new`
  obtain ⟨q, ⟨σe, hJe, -⟩, -, hc, -⟩ := hJ
  obtain ⟨hq0, -⟩ := wJ0_c0W hJe
  obtain ⟨_, ht⟩ := q.2.term
  rw [hq0, Spike.Lib.X64.WakeC0.c0W_term] at ht
  obtain ⟨hx, ha, hee⟩ := Expr.let_.inj ht
  have ha' := (Op.new.inj ha).1
  have hev := q.2.ev
  rw [hq0, ← ha'] at hev
  have hτ : q.1.τ = .int := (Prod.mk.inj (Option.some.inj hev)).1.symm
  rw [← hx, ← hee, hτ, hq0] at hc
  subst hc
  -- the thread pointer: the first TCB
  have hpin : (Ly).pinA.toNat < 2 ^ 32 := (Ly).words_small _ (Ly).pin_mem
  have hp0 := Spike.Lib.PlaceWX.pinA_toNat_ofPlaceWX hpw i
  have hpin8 : (tcbS (Ly)).toNat = (Ly).pinA.toNat + 8 := by
    show (Spike.Lib.X64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64).toNat = _
    rw [Spike.Lib.X64.Rt.pinA_lab0, BitVec.add_zero, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have htp8 : (tpOf (tcbS (Ly))).toNat = (Ly).pinA.toNat + 8 := by
    show (UInt64.ofNat (tcbS (Ly)).toNat).toNat = _
    rw [UInt64.toNat_ofNat', hpin8]; omega
  refine ⟨_, _, _, _, ⟨hRok, by omega, hRF, by rw [hRlo]; decide, by rw [hRhi]; decide⟩, ?_, hF0 _ m0 σC,
    ⟨⟨_, σC, rfl⟩, fun σe c h => ?_, by omega,
      Spike.Lib.X64.Flow.WakeWc.box_rsp hFm.2.2⟩, ⟨hA0, htp, htp8⟩, rfl, ⟨rfl, rfl, rfl, rfl⟩, ⟨?_, hu⟩,
    ⟨Spike.Lib.X64.WakePh.StartPlaceLy.wF_takeMem hpw i hA13,
      Spike.Lib.X64.WakeBoxW.wF_dmem
        (Spike.Lib.X64.WakeBoxW.fS_dmem (L := Ly) (rS := RS0) (Lsw := wcLsw) (k0 := 0#64) (v := topS (Ly) 0#64)), by rw [hRhi]; decide,
      Spike.Lib.X64.WakePh.StartPlaceLy.stackOff_r0_boxFp hpw i, by rw [hRlo]; decide, by rw [hRhi]; decide⟩⟩
  · -- the call's slots in the pool
    intro k h1 h2
    have := Spike.Lib.Region.addr_toNat_of hRok (k := k) (by rw [hRlo]; omega) (by rw [hRhi]; omega)
    constructor <;> omega
  · -- `%rdi` the first TCB
    obtain ⟨-, hx⟩ := wJ0_c0W h
    show σe.regs.rdi.toBitVec.toNat = _
    rw [hx]
    show (tpOf (tcbS (Ly))).toNat = _
    rw [htp8, hp0]; rfl
  · -- main's stack owned: off the region `StackOff`, inside it `Abs`
    refine ⟨by rw [Scc.Sem.Range.Sub, hr0, hr0s]; exact hst, fun a h8 ha ha7 => ?_⟩
    simp only [Scc.Sem.X64.privLoad, Option.isSome_map]
    exact load_of_off hRok (by omega) (by rw [hRlo]; decide) (by rw [hRhi]; decide) hSO hAbs a h8 ha ha7

/-- **`wake_start_wc_h0`'s `hxa`** at wake's arena and the one-box fragment
`I2 (arW hpw i) L0 ls0 inv0 inv1`: the box's landing with main's thread
pointer is in the memory side's allocation fragment. The cell `A` lands in
the arena (`AllocLand`, from `bX`'s allocator fact at `off = 8`,
`units ≥ 1`), and the landing, a `Box` (`box_landing`), is in `inv1` by
`h1`'s `Box` clause (`hB1`; from an `H1Stmt … (Box (Ly) MS F0) inv1` as
`fun l b n hl hb => (h1 l b n hl hb).2.1`), so in `I2`'s `inv1` disjunct.

OPEN `hUn1` (run-level, as AArch64's): the child's stack unmapped at the
landing (`KeepUn.U`). Its discharge: `U r1` holds of the loaded image and
is kept by every step up to the landing (`KeepUn.SegW.keepUn`). -/
theorem hxa_R (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    {μ : Scc.Sem.Marks} {rd : TermRun.Word → Prop} {cT : Loc} {L0 : Lbl} {ls0 : Lsize} {inv0 : FragS isa}
    {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa} {F0 : MachineData → Prop}
    (hB1 : ∀ l b n, L0 l = none → Spike.Lib.HeapLand.AllocLand (AR).heap (AR).cells b n →
      ∀ s c, Spike.Lib.X64.Flow.WakeWc.Box (Ly) (MS) F0 l b n s c → inv1 l b n s c [])
    (hF0 : ∀ v m0 σC m, wF (RS wcLsw v) wcD (FS (Ly) RS0 wcLsw 0#64 v) m0 σC m → F0 m)
    /- OPEN root obligation (run-level): the child's stack unmapped at the landing -/
    (hUn1 : ∀ v m0 σC l A s c, L0 l = none →
      At (Ly).exe (Ly).endPc ((wR (RS wcLsw v) wcD).fp (-8)) (wF (RS wcLsw v) wcD (FS (Ly) RS0 wcLsw 0#64 v) m0 σC)
        (bX (MS) (Ly).lab ((JW) σC) l A) s c → TPW s → Spike.Lib.X64.KeepUn.U R1 s) :
    ∀ v m0 σC l A s c, L0 l = none →
      At (Ly).exe (Ly).endPc ((wR (RS wcLsw v) wcD).fp (-8)) (wF (RS wcLsw v) wcD (FS (Ly) RS0 wcLsw 0#64 v) m0 σC)
        (bX (MS) (Ly).lab ((JW) σC) l A) s c → TPW s → (MS).xa l A 1 s c := by
  intro v m0 σC l A s c hl hA htp
  have hB := box_landing hpw i hA13 hF0 hA htp (hUn1 v m0 σC l A s c hl hA htp)
  obtain ⟨-, -, -, -, -, -, -, q, -, -, -, ob, hAo, hlt⟩ := hA
  obtain ⟨hu, hf⟩ := units_off (Λ := (Ly).Λ) q.2.toS.accs
  have hu' : 1 ≤ (MS).units 1 q.1.τ := hu
  have hf' : (MS).off 1 q.1.τ = 8 := hf
  have hcl : (MS).cells = 4194304 := rfl
  have hAL : Spike.Lib.HeapLand.AllocLand (AR).heap (AR).cells A 1 := by
    show (MS).heap + 8 ≤ A ∧ A + 8 * 1 ≤ (MS).heap + 16 * (MS).cells ∧ 1 + 1 ≤ (MS).cells
    rw [hf'] at hAo; omega
  exact ⟨hAL, .inr ⟨l, A, 1, hl, hAL, rfl, rfl, hB1 l A 1 hl hAL s c hB⟩⟩

end Spike.Lib.X64.WakePh.Hxa

/-- info: 'Spike.Lib.X64.WakePh.Hxa.wJ0_c0W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Hxa.wJ0_c0W

/-- info: 'Spike.Lib.X64.WakePh.Hxa.load_of_off' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Hxa.load_of_off

/-- info: 'Spike.Lib.X64.WakePh.Hxa.fp_geom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Hxa.fp_geom

/-- info: 'Spike.Lib.X64.WakePh.Hxa.box_landing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Hxa.box_landing

/-- info: 'Spike.Lib.X64.WakePh.Hxa.hxa_R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Hxa.hxa_R
