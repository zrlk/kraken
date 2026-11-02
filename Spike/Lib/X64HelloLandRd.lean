/-
**`wc_rodata`'s counter add's tail at hello's root, the child's stack unmapped, under main's thread pointer**
(x86-64; the twin of `Spike/Lib/A64HelloLandRd.lean`): from the allocator's `c2` after a counter add of
`wc_rodata`'s buffer call (`Land.GcRdH`, under main's frame `FR`), with `r1Of` unmapped and main's thread pointer,
the state is in the root's level-0 invariant `RootH0.inv0H` at the frames `[FR]`.

The segment from `c2` is the allocator's rest at a level-ending call (`Flow.seg_alloc_ofW_atNR`: its return is its
allocation, landing in the memory side's fragment; its only exit the heap abort `EX30 .abort`), resumed in
`wc_rodata`'s frame (`seg_resumeW`, the caller known through `RdCtx`) at `HelloRd.rX … .abort`. It runs inside
`NoSetFsW` at `tpXa (StartH0U.msUH … [FR]) t` (`HelloM.rdPreW_noMsrH`/`rdPreW_tpH`), so the landing is asked only
at the thread pointer and with `r1Of` unmapped: it is `StartH0H1.RdLandH`, handed to level 1's statement `h1`
(`StartH0H1.hRdU_of_h1F`). Then the thread pointer is kept (`Flow.SegW.keepTPN'`, `hrd` asked only at the thread
pointer: `WakeTP.tpG`); moved to `unXa (msBotH … [FR]) r1Of` (`WakePh.StartH0X.SegW.mono_xa`),
`KeepUn.SegW.keepUn` (the take of `rS0`, disjoint from `r1Of`) back to `msBotH`, lifted to `[FR]`
(`SegWS.liftS`), the abort closed by `RdHAb.hello_rd_hab_closed`, the take as `TakeCKS`, `WS` as `W0H`; the start
of a segment with no exit is in `inv0H` (`X64GfpS.gfpS_of_segWS`).

As at wake (`RootUL.HLandU`), the tail asks `U r1Of` at `c2`, and also `TP` (the landing level 1 takes has both);
neither is static at `c2` (the allocator's nodes and `CKept` pin neither), so the context must carry them.

- `HLandRdU`: `wc_rodata`'s counter add's tail with `U r1Of` and `TP` at `c2`.
- `hlandRd_U`: `HLandRdU` at `inv0H`, from `wc_rodata`'s `hrd` (`HrdS.hrd_WSHF`'s form at `J := JS Ly 0 c0S`),
  level 1's `h1` and `hhabctlRd` at `J1 := mRdJ0 (rdJH … (RS helloLsw top) …)` and the fragment `I3 … ⊥ inv1 inv2`
  (`msBotH`'s).

## Differences from the AArch64 version

- The counter add's tail starts at the allocator's `c2` (AArch64 `n4`): x86-64's `rmw` adds the counter in one
  instruction, its next node `c2` (as wake's `RootUL.HLandU`).
- `scc_rt_main`'s region at the new stack's base `v` is `MainGlue.RS helloLsw v` (AArch64 `swR v (-helloLsw) 0`);
  `wc_rodata`'s caller's entry invariant `rdJH` takes that region, so `J'` depends on `v` and `J1` is fixed at the
  first stack's top `topS Ly 0`.
- The thread pointer is `%fs`'s base `tpOf (tcbS Ly)`, kept inside `NoSetFsW` (AArch64 `NoMsrW`, `TPIDR_EL0`).
- The allocator's region `aR (mR R)` needs no base alignment (AArch64's `WcW.aRH_ok`): its `OK` is
  `Region.callee_ok`; `CallerCells` and `CKept` reach `8` (AArch64 `0`).
- The heap abort's exit carries its return address's slot (`rX .abort`'s `slot (-208)`, from `EX30 .abort`'s
  `slot (-160)` through `leave`; AArch64 `x30`).
- `SegWS`'s `mono_K`/`mono_W` are `WakePh.Land5.segWS_mono_K`/`segWS_mono_W` (AArch64 `SegWS.mono_K`/`mono_W`).
- The stacks' bound is `X64WakeHClC.hbd_W` (no `a13data` premise; AArch64 through `hsub1_W`), and the arena's
  `hmem` is `HrdArena.hmem_U`. The loader's facts are the two parses `cellsOf asm` (AArch64 `textProgram`).
-/
import Spike.Lib.X64HelloLandR
import Spike.Lib.X64HelloLand
import Spike.Lib.X64HelloRdHAbC
import Spike.Lib.X64HelloStartH0H1
import Spike.Lib.X64HelloRootH0
import Spike.Lib.X64HelloHrdArena
import Spike.Lib.X64HelloMainPreT
import Spike.Lib.X64HelloLand3
import Spike.Lib.X64Hello1RodataTP
import Spike.Lib.X64AllocNR
import Spike.Lib.X64CallResume
import Spike.Lib.X64KeepUn
import Spike.Lib.X64WakeStartH0X
import Spike.Lib.X64WakeHClC
import Spike.Lib.X64WakeTP
import Spike.Lib.X64GfpS
import Spike.Lib.X64WakeLand5
import Spike.Lib.LowerX64.LandHu

namespace Spike.Lib.X64.HelloPh.LandRd

variable {asm : Scc.Sem.X64.Asm}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Entry)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64ConsumerA (TakeCKS I3)
open Spike.Lib.X64.HelloPh (lo)
open Spike.Lib.X64.WakeWf (DtW)
open Spike.Lib.X64.HelloPh.StartGlue (X0WH)
open Spike.Lib.X64.HelloPh.StartWcS (WS rdJH)
open Spike.Lib.X64 (At enter)
open Spike.Lib.X64.Flow.Ret0 (CallerCells tpOf)
open Spike.Lib.X64.WakePh.MainGlue (FS JS RS tcbS topS)
open Spike.Lib.X64.Flow.Hello1 (AG mR mF mRdJ0 aR)
open Spike.Lib.X64.Flow.HelloRd (rN rX rXF RdPreW RdCtx)
open Spike.Lib.X64.KeepUn (U unXa)
open Spike.Lib.X64.KeepTP (TP tpXa)
open Spike.Lib.X64.HelloPh.StartH0H1 (RdLandH)
open Spike.Lib.X64.Alloc (Call N Ea)
open Spike.Lib.X64.HelloPh.StartH0G (helloLsw)
open Spike.Lib.X64.HelloPh.StartH0B (W0H)
open Spike.Lib.X64.HelloPh.StartH0U (msUH)
open Spike.Lib.X64.HelloPh.RootH0 (msBotH inv0H)
open Spike.Lib.X64.HelloPh.Land (CtrOkS refH GcRdH)
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib (FragS Frag SegWS MemSide PlaceWX Region)
open Spike.Lib.X64WakeLoadT (L0T ls0T)
open Spike.Lib.X64.HelloPh.C0S (c0S)
open Spike.Lib.X64HelloSrc (helloSrc)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.X64.AS

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (rd : TermRun.Word → Prop) (ls : Lsize)

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
/-- `wc_rodata`'s caller's entry invariant at the root, at `scc_rt_main`'s region `RS helloLsw v` (`Land`'s). -/
local notation "J'" => fun v : BitVec 64 => rdJH (Ly).lab (RS helloLsw v) (JS (Ly) 0#64 c0S)

set_option hygiene false in
/-- The first stack's top. -/
local notation "TOP" => topS (Ly) 0#64

set_option hygiene false in
/-- main's thread pointer. -/
local notation "TV" => tpOf (tcbS (Ly))

/-- **`wc_rodata`'s counter add's tail with `r1Of` unmapped, under main's thread pointer** (wake's
`RootUL.HLandU`): from the allocator's `c2` after a counter add of `wc_rodata`'s buffer call at a memory side
`ms0` that is `refH fs` but for `xa`, with `U r1Of` and `TP`, the state is in `Q` at the frames `fs`. The landing
level 1 takes (`StartH0H1.RdLandH`) has both. -/
def HLandRdU (Q : FragS isa) : Prop :=
  ∀ fs (ms0 : MemSide isa) R F q, ms0 = { refH (asm := asm) hpw i0 E rd ls fs with xa := ms0.xa } →
    GcRdH hpw i0 fs ms0 R F q → CtrOkS ms0 LBL R F q →
    ∀ s c, At (Ly).exe (Ly).endPc R F (N LBL ms0 q .c2) s c → U (R1) s → TP (TV) s → Q s c fs

variable (Ctx : FragS isa) (ls0 : Lsize) (inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa)
  (inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa)

set_option hygiene false in
/-- `msBotH`'s fragment: `I3` with its `inv0` disjunct `⊥`. -/
local notation "IB" => I3 (AR) (LB) (ls0T ls) (fun _ _ _ => False) inv1 inv2

set_option hygiene false in
/-- The root's start-form memory sides at `IB`. -/
local notation "MSU" => msUH (asm := asm) hpw i0 E rd (IB) ls

set_option hygiene false in
local notation "MSB" => msBotH (asm := asm) hpw IH E rd ls inv1 inv2

set_option hygiene false in
/-- The start's level at the root's choices. -/
local notation "WP" => WS (Ly) NT (AR) helloSrc DtW (Spike.Lib.X64.HelloPh.ClH (Ly)) Ctx (LB) (ls0T ls0) (FR)
  (X0WH (Ly) (AX))

set_option hygiene false in
/-- `wc_rodata`'s frame condition at the first stack's top. -/
local notation "FT" => mF (RS helloLsw (TOP)) (FS (Ly) (RS0) helloLsw 0#64 (TOP))

set_option hygiene false in
/-- `wc_rodata`'s region at the first stack's top. -/
local notation "MT" => mR (RS helloLsw (TOP))

set_option maxHeartbeats 1600000 in
/-- **`HLandRdU` at the root's level-0 invariant `inv0H`** (module doc): the allocator's rest from `c2` inside
`NoSetFsW` at `tpXa (msUH [FR])`, resumed at `rX .abort`, the thread pointer kept, moved to `msBotH` with `r1Of`
unmapped, closed by `hello_rd_hab_closed`. Premises: `wc_rodata`'s `hrd` (`HrdS.hrd_WSHF`'s form), level 1's
`h1` and `hhabctlRd` at `J1 := mRdJ0 (J' top)` and `I := I3 … ⊥ inv1 inv2`. -/
theorem hlandRd_U (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some SccCode.helloCells) (hlo0 : Λ0.code.lo = lo)
    (hc : Spike.Lib.X64.Rt.CtrZ o)
    (hrd : ∀ v m0 σC, RdPreW (Spike.Lib.X64.WakeTP.tpG (TV) fun s c => WP s c [FR]) KR (Ly).exe (Ly).endPc
      (mR (RS helloLsw v)) (mF (RS helloLsw v) (FS (Ly) (RS0) helloLsw 0#64 v) m0 σC) ((MSU) [FR])
      (mRdJ0 ((J') v) σC) (mRdJ0 ((J') v) σC))
    {W1 : WeakMem.AllocLabel → Nat → Nat → FragS isa} {K : State → State → Prop}
    {ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isa}
    /- level 1's statement: rodata's landing is in `inv1 … [FR]` -/
    (h1 : Spike.Lib.X64HelloPreA.H1StmtHF W1 K (AR) (LB) ms1 (Ly)
      (RdLandH (asm := asm) hpw i0 E rd (IB) ls (fun σC => mRdJ0 ((J') (TOP)) σC)) inv1 [FR])
    (hhabctlRd : ∀ σC, Spike.Lib.X64.HelloPh.HabCtlRd.HabCtlRdH ((MSB) [FR]) (Ly).lab helloSrc (Ly).Λ (LB)
      (MT) (AR) [FR] (mRdJ0 ((J') (TOP)) σC)) :
    HLandRdU (asm := asm) hpw i0 E rd ls (inv0H (asm := asm) hpw IH E rd Ctx ls0 ls (FR) inv1 inv2) := by
  intro fs ms0 R F q hms hG _ s c hAt hU hT
  obtain ⟨X, rfl⟩ : ∃ X, ms0 = { refH (asm := asm) hpw i0 E rd ls fs with xa := X } := ⟨_, hms⟩
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
  -- the arena's facts at `msUH`
  have hcl : ((MSU) [FR]).cells = 4194304 := rfl
  have hqU : q.OK ((MSU) [FR]) (Ly).lab := { hq with }
  have hqT : q.OK (tpXa ((MSU) [FR]) (TV)) (Ly).lab := Spike.Lib.X64.Flow.Hello1.callOK_tp hqU
  have hmem := Spike.Lib.X64.HelloPh.HrdArena.hmem_U (asm := asm) hpw i0 (E := E) (rd := rd) (I := IB) (ls := ls)
    (fs := [FR]) hc (k0 := 0#64) (v := TOP)
  have hRdU := Spike.Lib.X64.HelloPh.StartH0H1.hRdU_of_h1F hpw i0 E h1
  -- the landing at `tpXa (msUH [FR])`: one the arena hands out (`Ea` at `arOf`), the rest `h1`'s given `U r1Of`
  -- and the thread pointer
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
    (fun a ha m hm => hmem q hqU a ha m hm.1.1) hxa
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
    -- the thread pointer kept; at `unXa (msBotH [FR]) r1Of`, then `keepUn`, lifted to `[FR]`
    have hS0 := Spike.Lib.X64.Flow.SegW.keepTPN' rfl hS fun _ _ h ht => h ht
    have hS1 := Spike.Lib.X64.WakePh.StartH0X.SegW.mono_xa (ms' := unXa ((MSB) [FR]) (R1)) hS0 rfl
      fun _ _ _ _ _ h hU' => ⟨h.1, h.2 hU'⟩
    have hS2 := Spike.Lib.X64.KeepUn.SegW.keepUn rfl hS1 fun _ _ _ s' hk hs => by
      obtain ⟨-, pm, rfl⟩ := hk; exact Spike.Lib.X64.KeepUn.take_un pm hd hw1 hwS hs
    have hL := Spike.Lib.SegWS.liftS (W := fun s c fs => WP s c fs) (ms := MSB) [FR] hS2 fun _ _ h => h
    -- the abort closed; the take as `TakeCKS`; `WS` as `W0H`
    have hC := Spike.Lib.X64.HelloPh.RdHAb.hello_rd_hab_closed hpw IH (Ctx := Ctx) (ls0 := ls0)
      (J1 := fun σC => mRdJ0 ((J') (TOP)) σC) hpa hhp hlo0 hhabctlRd
    refine Spike.Lib.X64GfpS.gfpS_of_segWS (Spike.Lib.X64.WakePh.Land5.segWS_mono_W
      (Spike.Lib.X64.WakePh.Land5.segWS_mono_K ((hL.mono_post ?_).seq hC)
        fun s c fs hW s' => Spike.Lib.X64.HelloPh.StartH0B.takeCKS_iffH hpw IH hW.2.1)
      (W' := W0H (asm := asm) hpw IH E DtW Ctx (ls0T ls0) (FR)) fun s c fs h => ?_) s c [FR] ⟨⟨⟨hAt, hT⟩, hU⟩, rfl⟩
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

end Spike.Lib.X64.HelloPh.LandRd

/-- info: 'Spike.Lib.X64.HelloPh.LandRd.hlandRd_U' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.LandRd.hlandRd_U
