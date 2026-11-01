/-
**`wc_rodata`'s counter add's tail at hello's root, the child's stack unmapped, under main's thread pointer**
(AArch64; the twin of `Spike/Lib/A64WakeLandU.lean`'s `hland_RU` at `wc_rodata`'s buffer
call): from the allocator's `n4` after a counter add of `wc_rodata`'s buffer call (`Land.GcRdH`, under main's frame
`FR`), with `r1Of` unmapped and main's thread pointer, the state is in the root's level-0 invariant `RootH0.inv0H`
at the frames `[FR]`.

The segment from `n4` is the allocator's rest at a level-ending call (`Flow.seg_alloc_ofW_atNR`: its return is its
allocation, landing in the memory side's fragment; its only exit the heap abort `EX30 .abort`), resumed in
`wc_rodata`'s frame (`Flow.seg_resumeW`, the caller known through `RdCtx`) at `HelloRd.rX … .abort`. It runs inside
`NoMsrW` at `tpXa (StartH0U.msUH … [FR]) t` (`HelloM.rdPreW_noMsrH`/`rdPreW_tpH`, as `HelloM.hello_main_pre_segWSTF`),
so the landing is asked only at the thread pointer and with `r1Of` unmapped: it is `StartH0H1.RdLandH`, handed to
level 1's statement `h1` (`StartH0H1.hRdU_of_h1F`, as `StartH0U1.hst0_ofHU1_i0`). Then the thread pointer is kept
(`Flow.SegW.keepTPN'`, `hrd` asked only at the thread pointer: `WakeWc.tpG`, L0-tpG); as
`StartH0U0.hst0_ofHU0_i0`: moved to `unXa (msBotH … [FR]) r1Of` (`WakePh.StartH0U.SegW.mono_xa`),
`KeepUn.SegW.keepUn` (the take of `rS0`, disjoint from `r1Of`) back to `msBotH`,
lifted to `[FR]` (`SegWS.liftS`), the abort closed by `RdHAb.hello_rd_hab_closed`, the take as `TakeCKS`, `WS` as
`W0H`; the start of a segment with no exit is in `inv0H` (`A64GfpS.gfpS_of_segWS`).

As at wake (`RootUL.HLandU`), the tail asks `U r1Of` at `n4`, and also `TP` (the landing level 1 takes has both);
neither is static at `n4` (the allocator's nodes and `CKept` pin neither), so the context must carry them. That
context (wake's `RootUL.CtxRU`) is not here.

- `HLandRdU`: `LandR.HLandRd` with `U r1Of` and `TP` at `n4`.
- `hlandRd_U`: `HLandRdU` at `inv0H`, from `wc_rodata`'s `hrd`, level 1's `h1` and `hhabctlRd` in
  `StartH0U1.hst0_ofHU1_i0`'s forms at `J1 := mRdJ0 J'` (`HrdS.hrd_WSHF`'s) and the fragment `I3 … ⊥ inv1 inv2`
  (`msBotH`'s).
-/
import Spike.Lib.A64HelloLandR
import Spike.Lib.A64CallResume
import Spike.Lib.A64HelloRdPreWI
import Spike.Lib.A64WakeStartH0U
import Spike.Lib.A64HelloStartH0U1

namespace Spike.Lib.A64.HelloPh.LandRd

variable {asm : String}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Entry)
open Scc.Sem.A64 (textProgram)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64ConsumerA (TakeCKS I3)
open Spike.Lib.A64.WakePh (lo)
open Spike.Lib.A64.WakeWf (DtW)
open Spike.Lib.A64.HelloPh.StartGlue (X0WH)
open Spike.Lib.A64.HelloPh.StartWcS (WS rdJH)
open Spike.Lib.A64.Flow (swR At enter)
open Spike.Lib.A64.Flow.Ret0 (CallerCells)
open Spike.Lib.A64.WakePh.MainGlue (FS JS)
open Spike.Lib.A64.Flow.Hello1 (AG mR mF mRdJ0 aR)
open Spike.Lib.A64.Flow.HelloRd (rN rX rXF RdPreW RdCtx)
open Spike.Lib.A64.KeepUn (U unXa)
open Spike.Lib.A64.KeepTP (TP tpXa)
open Spike.Lib.A64.HelloPh.StartH0H1 (RdLandH)
open Spike.Lib.A64.Alloc (Call N Ea)
open Spike.Lib.A64.HelloPh.StartH0G (helloLsw)
open Spike.Lib.A64.HelloPh.StartH0B (W0H)
open Spike.Lib.A64.HelloPh.StartH0U (msUH)
open Spike.Lib.A64.HelloPh.RootH0 (msBotH inv0H)
open Spike.Lib.A64.HelloPh.Land (CtrOkS refH GcRdH)
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib (FragS Frag SegWS MemSide)
open Spike.Lib.WakeLoadT (L0T ls0T)
open Spike.Lib.A64.HelloPh.C0S (c0S)
open Spike.Lib.HelloSrc (helloSrc)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.A64.Flow.AS

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (rd : TermRun.Word → Prop) (ls : Lsize)

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
local notation "R1" => Spike.Lib.A64.Rt.PreChild.r1Of (Ly).lab

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

set_option hygiene false in
/-- The allocator's labels. -/
local notation "LBL" => (_root_.Executable.labels (Ly).exe).label

set_option hygiene false in
local notation "AX" => (Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL

set_option hygiene false in
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
local notation "TV" => UInt64.ofBitVec (Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64)

/-- **`wc_rodata`'s counter add's tail with `r1Of` unmapped, under main's thread pointer** (`LandR.HLandRd` with
`U r1Of` and `TP` at `n4`, wake's `RootUL.HLandU`): the landing level 1 takes (`StartH0H1.RdLandH`) has both. -/
def HLandRdU (Q : FragS isaLSE2) : Prop :=
  ∀ fs (ms0 : MemSide isaLSE2) R F q, ms0 = { refH (asm := asm) hpw i0 E rd ls fs with xa := ms0.xa } →
    GcRdH hpw i0 fs ms0 R F q → CtrOkS ms0 LBL R F q →
    ∀ s c, At (Ly).exe (Ly).endPc R F (N LBL ms0 q .n4) s c → U (R1) s → TP (TV) s → Q s c fs

variable (Ctx : FragS isaLSE2) (ls0 : Lsize) (inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2)
  (inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2)

set_option hygiene false in
/-- `msBotH`'s fragment: `I3` with its `inv0` disjunct `⊥`. -/
local notation "IB" => I3 (AR) (LB) (ls0T ls) (fun _ _ _ => False) inv1 inv2

set_option hygiene false in
/-- The root's start-form memory sides at `IB` (`hst0_ofHU_i0`'s `MSU`). -/
local notation "MSU" => msUH (asm := asm) hpw i0 E rd (IB) ls

set_option hygiene false in
local notation "MSB" => msBotH (asm := asm) hpw IH E rd ls inv1 inv2

set_option hygiene false in
/-- The start's level at the root's choices. -/
local notation "WP" => WS (Ly) NT (AR) helloSrc DtW (Spike.Lib.A64.HelloPh.ClH (Ly)) Ctx (LB) (ls0T ls0) (FR)
  (X0WH (Ly) (AX))

/-- **`HLandRdU` at the root's level-0 invariant `inv0H`** (module doc): the allocator's rest from `n4` inside
`NoMsrW` at `tpXa (msUH [FR])`, resumed at `rX .abort`, the thread pointer kept, moved to `msBotH` with `r1Of`
unmapped, closed by `hello_rd_hab_closed`. Premises: `wc_rodata`'s `hrd`, level 1's `h1` and `hhabctlRd` in
`StartH0U1.hst0_ofHU1_i0`'s forms at
`J1 := mRdJ0 J'` and `I := I3 … ⊥ inv1 inv2`. -/
theorem hlandRd_U (hpa : textProgram asm = .ok o.prog)
    (hhp : textProgram asm = .ok SccCode.helloProg) (hlo0 : Λ0.code.lo = lo)
    (hc : Spike.Lib.A64.Rt.CtrZ o) (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    (hrd : ∀ v m0 σC, RdPreW (Spike.Lib.A64.Flow.WakeWc.tpG (TV) fun s c => WP s c [FR]) KR (Ly).exe (Ly).endPc
      (mR (swR v (-helloLsw) 0)) (mF (swR v (-helloLsw) 0) (FS (Ly) RS helloLsw 0#64 v) m0 σC) ((MSU) [FR])
      (mRdJ0 (J') σC) (mRdJ0 (J') σC))
    {W1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2} {K : State → State → Prop}
    {ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isaLSE2}
    /- level 1's statement (as `StartH0U1.hst0_ofHU1_i0`'s): rodata's landing is in `inv1 … [FR]` -/
    (h1 : Spike.Lib.HelloPreA.H1StmtHF W1 K (AR) (LB) ms1 (Ly)
      (RdLandH (asm := asm) hpw i0 E rd (IB) ls (fun σC => mRdJ0 (J') σC)) inv1 [FR])
    (hhabctlRd : ∀ σC, Spike.Lib.A64.HelloPh.HabCtlRd.HabCtlRdH ((MSB) [FR]) (Ly).lab helloSrc (Ly).Λ (LB) (AR)
      [FR] (mRdJ0 (J') σC)) :
    HLandRdU (asm := asm) hpw i0 E rd ls (inv0H (asm := asm) hpw IH E rd Ctx ls0 ls (FR) inv1 inv2) := by
  intro fs ms0 R F q hms hG hok s c hAt hU hT
  obtain ⟨X, rfl⟩ : ∃ X, ms0 = { refH (asm := asm) hpw i0 E rd ls fs with xa := X } := ⟨_, hms⟩
  obtain ⟨rfl, hq, v, m0, σC, rfl, rfl, hra⟩ := hG
  -- the frame condition pins `v` at the first stack's top
  by_cases hv : v = TOP
  case neg =>
    obtain ⟨-, -, -, -, _, -, hF, -⟩ := hAt
    exact (hv hF.1.1.2.1.1).elim
  subst hv
  -- the layout's facts
  have hprog : (Ly).prog = SccCode.helloProg := Except.ok.inj (hpa.symm.trans hhp)
  have hpL : textProgram asm = .ok (Ly).prog := by rw [hprog]; exact hhp
  have hpS : Scc.Cert.Rt.A64.Lays (Ly).exe SccCode.helloProg (Ly).pfx := hprog ▸ (Ly).lays
  have hendS : (Ly).endPc = Scc.Cert.Rt.A64.endOf (Ly).exe SccCode.helloProg (Ly).pfx := by rw [← hprog]
  -- the ranges: `r1Of` in the pool, disjoint from `rS0`, both in the address space
  have hsub1 := Spike.Lib.A64.WakePh.StartPlaceLy.hsub1_W hpw IH hA13
  have hbd' : (Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab).toNat + 32768 < 2 ^ 64 := by
    rw [(Ly).lab_stacks]; exact Spike.Lib.WakeHClW.hbd_W hpw IH hsub1
  obtain ⟨h1l, h1s⟩ := Spike.Lib.A64.Rt.Ti2.r1Of_eq hbd'
  rw [(Ly).lab_stacks] at h1l hbd'
  have hSl : (RS).lo = (Ly).stacksA.toNat := by
    show ((Ly).stacksA + 0#64).toNat = _; rw [BitVec.add_zero]
  have hSs : (RS).size = 16384 := rfl
  have hw1 : (R1).lo + (R1).size ≤ 2 ^ 64 := by omega
  have hwS : (RS).lo + (RS).size ≤ 2 ^ 64 := by omega
  have hd : (R1).Disjoint (RS) := by unfold Scc.Sem.Range.Disjoint; omega
  -- the regions: `wc_rodata`'s at the call, the allocator's
  obtain ⟨hok0, hal0, hF0⟩ := Spike.Lib.A64.HelloPh.Land.fstable_FS hpw i0
  obtain ⟨hmR, halR, hFm⟩ := Spike.Lib.A64.Flow.Hello1.mR_ok hok0 hal0 hF0
    (by show (-helloLsw : Int) ≤ -288; decide) (by show (0 : Int) ≤ 0; decide) m0 σC
  obtain ⟨haR, halA⟩ := Spike.Lib.A64.HelloPh.WcW.aRH_ok hmR halR
    (by show (-208 : Int) ≤ -208; decide) (by show (0 : Int) ≤ 0; decide)
  -- the arena's facts at `msUH`
  have hwf := Spike.Lib.PlaceW.wf_link_of_placeW IH hpw
  have hsz : 16 * Scc.Cert.PlaceOK.allocCells ≤ (Ly).Λ.heap.size :=
    Spike.Lib.A64.Rt.ArenaW.PlaceW.heapSize_of_placeW (Spike.Lib.PlaceW.link IH hpw)
  have hb : (Ly).Λ.heap.lo + (Ly).Λ.heap.size ≤ 2 ^ 32 :=
    Spike.Lib.A64.Rt.ArenaW.heap_below_of_placeW (Spike.Lib.PlaceW.link IH hpw)
  have hdb : (Ly).Λ.data.lo + (Ly).Λ.data.size ≤ 2 ^ 32 :=
    Spike.Lib.A64.Rt.ArenaW.data_below_of_placeW (Spike.Lib.PlaceW.link IH hpw)
  obtain ⟨hc1, hc2, -⟩ := Spike.Lib.A64.Rt.ArenaW.ctr_item_of_placeW (Spike.Lib.PlaceW.link IH hpw) hc
  have hc1' : (Ly).Λ.data.lo ≤ Scc.Cert.PlaceOK.heapUseOf (Ly).Λ := hc1
  have hc2' : Scc.Cert.PlaceOK.heapUseOf (Ly).Λ + 8 ≤ (Ly).Λ.data.lo + (Ly).Λ.data.size := hc2
  have hA : Scc.Cert.PlaceOK.allocCells = 4194304 := rfl
  have hh : ((MSU) [FR]).heap = (Ly).Λ.heap.lo := rfl
  have hcl : ((MSU) [FR]).cells = 4194304 := rfl
  have hct : ((MSU) [FR]).ctr = Scc.Cert.PlaceOK.heapUseOf (Ly).Λ := rfl
  have hoff : ∀ q : Call, q.OK ((MSU) [FR]) (Ly).lab →
      ((MSU) [FR]).off q.n q.τ ≤ 16 * ((MSU) [FR]).units q.n q.τ := fun q hq => by
    have hu : 1 ≤ ((MSU) [FR]).units q.n q.τ := Spike.Lib.LowerA64.arOf_units_pos (Λ := (Ly).Λ) hq.accs
    have hf : ((MSU) [FR]).off q.n q.τ = 8 := Spike.Lib.LowerA64.arOf_off_eq (Λ := (Ly).Λ) hq.accs
    rw [hf]; omega
  have hH : (Ly).Λ.heap.lo ≤ ((MSU) [FR]).heap := Nat.le_of_eq hh.symm
  have hHi : ((MSU) [FR]).heap + 16 * ((MSU) [FR]).cells ≤ (Ly).Λ.heap.lo + (Ly).Λ.heap.size := by
    rw [hh, hcl]; omega
  have hctr : Spike.Lib.DmemPriv.WordIn (Ly).Λ.heap ((MSU) [FR]).ctr ∨
      Spike.Lib.DmemPriv.WordIn (Ly).Λ.data ((MSU) [FR]).ctr :=
    .inr (by unfold Spike.Lib.DmemPriv.WordIn Scc.Sem.Range.contains; rw [hct]; omega)
  have hmem := Spike.Lib.A64.Alloc.hmem_of_wordsNone (ms := (MSU) [FR]) (lab := (Ly).lab)
    (F := fun m => mF (swR (TOP) (-helloLsw) 0) (FS (Ly) RS helloLsw 0#64 (TOP)) m0 σC m ∧
      CallerCells (mR (swR (TOP) (-helloLsw) 0)) (-48) (-160) 0 m ∧
      RdCtx ((MSU) [FR]) (Ly).lab (mR (swR (TOP) (-helloLsw) 0)) (mRdJ0 (J') σC) (mRdJ0 (J') σC) q m)
    hwf (fun _ h => h.1.1.1.wn) hH hHi hctr hoff
  have hqU : q.OK ((MSU) [FR]) (Ly).lab := { hq with }
  have hqT : q.OK (tpXa ((MSU) [FR]) (TV)) (Ly).lab := Spike.Lib.A64.Flow.Hello1.callOK_tp hqU
  have hRdU := Spike.Lib.A64.HelloPh.StartH0H1.hRdU_of_h1F hpw i0 E h1
  -- the landing at `tpXa (msUH [FR])`: one the arena hands out (`Ea` at `arOf`), the rest `h1`'s given `U r1Of`
  -- and the thread pointer
  have hxa : ∀ l b w s c, (LB) l = none →
      At (Ly).exe (Ly).endPc (aR (mR (swR (TOP) (-helloLsw) 0)))
        (fun m => mF (swR (TOP) (-helloLsw) 0) (FS (Ly) RS helloLsw 0#64 (TOP)) m0 σC m ∧
          CallerCells (mR (swR (TOP) (-helloLsw) 0)) (-48) (-160) 0 m ∧
          RdCtx (tpXa ((MSU) [FR]) (TV)) (Ly).lab (mR (swR (TOP) (-helloLsw) 0)) (mRdJ0 (J') σC)
            (mRdJ0 (J') σC) q m)
        (Ea (tpXa ((MSU) [FR]) (TV)) q l b w) s c → (tpXa ((MSU) [FR]) (TV)).xa l b w s c := by
    intro l b w s c hl hA' ht
    replace hA' : At (Ly).exe (Ly).endPc (aR (mR (swR (TOP) (-helloLsw) 0))) _ (Ea ((MSU) [FR]) q l b w) s c := hA'
    have hAL : AllocLand (AR).heap (AR).cells b w := by
      obtain ⟨-, -, -, -, -, -, -, -, old, -, -, hb', hold, -, -, -, us, hus, hw⟩ := id hA'
      have hf : ((MSU) [FR]).off q.n q.τ = 8 := Spike.Lib.LowerA64.arOf_off_eq (Λ := (Ly).Λ) hqU.accs
      have hu : ((MSU) [FR]).units q.n q.τ = q.n * TermRun.nWords us + 1 :=
        Spike.Lib.Arena.ofWords_units_fit (heap := (Ly).Λ.heap.lo) (cells := Scc.Cert.PlaceOK.allocCells)
          (ctr := Scc.Cert.PlaceOK.heapUseOf (Ly).Λ) (m := fun _ => 0) (by decide) hus
          (Nat.le_trans (Nat.le_add_left _ old) hold)
      show ((MSU) [FR]).heap + 8 ≤ b ∧ b + 8 * w ≤ ((MSU) [FR]).heap + 16 * ((MSU) [FR]).cells ∧
        w + 1 ≤ ((MSU) [FR]).cells
      rw [hf] at hb'; rw [hu, hcl] at hold; rw [hcl]; subst hw
      omega
    exact ⟨hAL, fun hU' => hRdU (TOP) m0 σC ⟨q, hqU⟩ _ (fun _ h => h.1)
      (fun _ ⟨_, _, h⟩ => h) l b w s c hl hA' hAL hU' ht⟩
  -- the allocator's rest from `n4` inside `NoMsrW`, at `tpXa`, its only exit the heap abort
  have hAl := Spike.Lib.A64.Flow.seg_alloc_ofW_atNR (p := helloSrc) (lbl := LB) hpS hendS
    Spike.Lib.A64.Flow.HelloRd.hello_alloc
    (Spike.Lib.A64.HelloPh.Land.fstable_aRH hmR hFm (by show (-208 : Int) ≤ -208; decide)
      (by show (0 : Int) ≤ 0; decide))
    haR halA (by simp [Spike.Lib.Region.callee]) (by simp [Spike.Lib.Region.callee]) hqT
    (fun a ha m hm => hmem q hqU a ha m hm) hxa
    ((Spike.Lib.A64.Flow.HelloM.rdPreW_tpH (t := TV)
      (Spike.Lib.A64.Flow.HelloM.rdPreW_noMsrH hpS hendS (hrd (TOP) m0 σC))).alloc q hqT hra) .n4
  -- its exit resumed in `wc_rodata`'s frame
  have hres := Spike.Lib.A64.Flow.seg_resumeW (N := fun e : Empty => e.elim)
    (E := rXF (tpXa ((MSU) [FR]) (TV)) (Ly).lab (LB) (mRdJ0 (J') σC))
    (F₂ := mF (swR (TOP) (-helloLsw) 0) (FS (Ly) RS helloLsw 0#64 (TOP)) m0 σC) (M := fun _ => True)
    (PC := fun σC' => ∃ c, (rN (Ly).lab (mRdJ0 (J') σC) (mRdJ0 (J') σC) .call).J σC' c ∧
      (N (Ly).lab (tpXa ((MSU) [FR]) (TV)) q .e).J (enter (-48) σC') c)
    (Ex := fun _ : Unit => Spike.Lib.A64.Alloc.EX30 (Ly).lab (tpXa ((MSU) [FR]) (TV)) q (LB) .abort)
    (hAl.mono_post fun _ _ h => ⟨(), h, trivial⟩)
    (fun m ⟨h1, _, mC, σC', c', hA', hJ1, hJ2, hK'⟩ => ⟨h1, mC, σC', ⟨-48, []⟩, hK', hA', c', hJ1, hJ2⟩)
    (fun _ h _ => h) ?_
  · have hS := hres.mono_post (Q' := At (Ly).exe (Ly).endPc (mR (swR (TOP) (-helloLsw) 0))
        (mF (swR (TOP) (-helloLsw) 0) (FS (Ly) RS helloLsw 0#64 (TOP)) m0 σC)
        (rX (tpXa ((MSU) [FR]) (TV)) (Ly).lab (LB) (mRdJ0 (J') σC) .abort)) fun s c h => by
      rcases h with ⟨e, -⟩ | ⟨y, h⟩
      · exact e.elim
      · cases y
        · obtain ⟨-, -, -, -, σ, -, -, hJ⟩ := h
          exact hJ.elim
        · exact h
    -- the thread pointer kept; at `unXa (msBotH [FR]) r1Of`, then `keepUn`, lifted to `[FR]`
    have hS0 := Spike.Lib.A64.Flow.SegW.keepTPN' rfl hS fun _ _ h ht => h ht
    have hS1 := Spike.Lib.A64.WakePh.StartH0U.SegW.mono_xa (ms' := unXa ((MSB) [FR]) (R1)) hS0 rfl
      fun _ _ _ _ _ h hU' => ⟨h.1, h.2 hU'⟩
    have hS2 := Spike.Lib.A64.KeepUn.SegW.keepUn rfl hS1 fun _ _ _ s' hk hs => by
      obtain ⟨-, pm, rfl⟩ := hk; exact Spike.Lib.A64.KeepUn.take_un pm hd hw1 hwS hs
    have hL := Spike.Lib.SegWS.liftS (W := fun s c fs => WP s c fs) (ms := MSB) [FR] hS2 fun _ _ h => h
    -- the abort closed; the take as `TakeCKS`; `WS` as `W0H`
    have hC := Spike.Lib.A64.HelloPh.RdHAb.hello_rd_hab_closed hpw IH (Ctx := Ctx) (ls0 := ls0)
      (J1 := fun σC => mRdJ0 (J') σC) hpa hhp hlo0 hhabctlRd
    refine Spike.Lib.A64GfpS.gfpS_of_segWS ((((hL.mono_post ?_).seq hC).mono_K
        fun s c fs hW s' => Spike.Lib.A64.HelloPh.StartH0B.takeCKS_iffH hpw IH hW.2.1).mono_W
      (W' := W0H (asm := asm) hpw IH E DtW Ctx (ls0T ls0) (FR)) fun s c fs h => ?_) s c [FR] ⟨⟨⟨hAt, hT⟩, hU⟩, rfl⟩
    · rintro s c fs ⟨⟨⟨hX, -⟩, -⟩, hfs⟩
      obtain ⟨he, hn, hdc, hpc, σ, hAb, hF, hX0, hX30, q', hq', hJ⟩ := hX
      exact ⟨⟨TOP, m0, σC, ⟨he, hn, hdc, hpc, σ, hAb, hF, hX0, hX30,
        ⟨q'.1, { q'.2 with }⟩, hq', hJ⟩⟩, hfs⟩
    · show Spike.Lib.A64.WakeWf.W0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ s c fs
      rw [Spike.Lib.A64.Flow.Worker.Wake.AbOffW.marks_target (Ly) hpL]; exact h
  -- the allocator's heap abort lands at `wc_rodata`'s
  rintro ⟨⟩ σx c' σC' hx ⟨c, ⟨⟨σe, hJe, -, -⟩, -, -, -, -⟩, ⟨hc, -, -, -⟩⟩
  obtain ⟨h2, h30x, hfull⟩ := hx
  exact .inr ⟨.abort, rfl, rfl, h2, h30x, ⟨q, hqT⟩, hfull, σe, hc ▸ hJe⟩

end Spike.Lib.A64.HelloPh.LandRd

/-- info: 'Spike.Lib.A64.HelloPh.LandRd.hlandRd_U' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.LandRd.hlandRd_U
