/-
**`hWp`'s top case at the root, inside `WSX`** (wake.w, x86-64):
`StartPlace.wake_start_wc_placeX`'s `hWp` at the first stack's top, at the
root's memory side `tpXa (Land.refW …) t` and context `Land.CtxR`, the
level `OwnImp.WSX` (owned words `ownGXW`), inside `NoSetFsW`, guarded by
main's thread pointer; then at every base by `hWp_W`.

- `offW_own`: the owned words (the four counters and `ntA`) are off
  `arW`'s cells and its counter.
- `hoffQ_R`: at a box call the header offset fits the cell.
- `hTopP_R`: `wcPreW_WSOg` at the top, its `SFactsSt2` from `ownGXW`'s
  producers (`OwnWc.proW_wcGX`, `eW_wcGX`, `OwnAlloc.allocW_wcGX`), its
  counter context from `Land.hctx_R`, its placement from `WcPl.hplP_W`.
- `hWp_R`: every base.

x86-64 twin of `Spike/Lib/A64WakeWcWfR.lean`'s `offW_own`, `hTopP_Rpl`,
`hTopP_R` (namespace `Spike.Lib.X64.WakePh.WcWfR`). **Where this differs
from AArch64**: the level is `WSX` at `ownGXW` (A64 `WS` at `ownG`), so the
`SFactsSt2` come from `ownGXW`'s producers, whose separation premises are
discharged here (`tcbSep_W`, `tcbM_ne_ntA_W`, `tcb2_notG_W` from `hA13`;
the bands by `top_band`, `top_bandA`; `hnoM` by `ctrSep_of_rtWordsOk` and
`ne_tcbM_of_heap`); the wrapper is `NoSetFsW` (A64 `NoMsrW`); the entry
control `c0` is generic with its facts `hc0`, `hpl0` premises (A64 at
`c0W`), as are `Dt`, `Cl` (`hcl`), the take pc `ax` (`hax`) and `frM`
(A64 `DtW`, `ClW`, `aW`); the invariant is `refW`'s (`⊥`; A64 any `I`);
`hpo : o.prog = wakeCells` and `hlo` replace A64's `hpa`/`hwp`/`hlo0`;
the placement is closed here (no separate `hTopP_Rpl`).
-/
import Spike.Lib.X64WakeWcTop
import Spike.Lib.X64WakeLand3
import Spike.Lib.X64WakeOwnSW
import Spike.Lib.X64WakeOwnT2W
import Spike.Lib.X64WakeOwnBoxM
import Spike.Lib.X64WakeWfCalOff
import Spike.Lib.X64WakeOwnImp

namespace Spike.Lib.X64.WakePh.WcWfR

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (codeLabel pcOf abi)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lsize)
open Spike.Lib.X64.WakePh.MainGlue (FS JS RS topS tcbS)
open Spike.Lib.X64.WakePh.StartFacts (wcD wcLsw)
open Spike.Lib.X64.Flow.Ret0 (tpOf)
open Spike.Lib.X64.Flow.WakeM (wR wF wJ0 wNC)
open Spike.Lib.X64.Flow.WakeWc (WcPreW WcSp0W wAR)
open Spike.Lib.X64.KeepTP (TP tpXa)
open Spike.Lib.X64.WakeTP (tpG)
open Spike.Lib.X64.Alloc (Call)
open Spike.Lib.X64.Rt.Reserve (ntA)
open Spike.Lib (PlaceWX)
open Scc.Sem (Entry)
open Spike.Lib.X64WakeLoadT (L0T ls0T)
open Spike.Lib.X64WakeT1 (wakeSrc)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (asm : Scc.Sem.X64.Asm) (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (c0 : Ctl) (ls0 : Entry → Lsize)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

set_option hygiene false in
local notation "RS0" => Spike.Lib.X64.Rt.rS0 (Ly)

set_option hygiene false in
/-- The take (`PhRec.K`). -/
local notation "KW" => Spike.Lib.X64.PhRec.K (Ly) (RS0)

set_option hygiene false in
/-- Main's thread pointer. -/
local notation "TV" => tpOf (tcbS (Ly))

set_option hygiene false in
/-- The top of the first stack. -/
local notation "TOP" => topS (Ly) 0#64

set_option hygiene false in
/-- `wc_main`'s entry invariant from the caller's state. -/
local notation "JW" => fun σC => wJ0 (wNC (Ly).lab (JS (Ly) 0#64 c0)).J σC

set_option hygiene false in
/-- The root's memory side at entry `E`. -/
local notation "MR" => tpXa (Spike.Lib.X64.WakePh.Land.refW asm hp i ls0 E) (TV)

set_option hygiene false in
/-- The start's level at `ownGXW` at the root's context. -/
local notation "WSR" => Spike.Lib.X64.WakePh.WSX (Ly) (ntA (Ly).lab) (Spike.Lib.X64.WakeOD.arW hp i) wakeSrc Dt Cl
  (Spike.Lib.X64.WakePh.Land.CtxR (Ly) c0 (Spike.Lib.X64.WakePh.Land.refW asm hp i ls0 E)) (L0T (Ly).Λ)
  (ls0T (ls0 E)) frM (Spike.Lib.X64.WakeWf.X0W (Ly) ax)

/-- **The owned words are off `arW`'s cells and its counter**: the four
counters (runtime words, `ctrSep_of_rtWordsOk`) and `scc_rt_nthreads`
(`CalWf.hoffN_W`). -/
theorem offW_own (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true) :
    ∀ w', (w' = (Ly).pnA ∨ w' = (Ly).lockA ∨ w' = (Ly).freeNA ∨ w' = (Ly).nextA ∨ w' = ntA (Ly).lab) →
      ¬ ((Spike.Lib.X64.WakeOD.arW hp i).heap ≤ w'.toNat ∧
        w'.toNat < (Spike.Lib.X64.WakeOD.arW hp i).heap + 16 * (Spike.Lib.X64.WakeOD.arW hp i).cells) ∧
      w' ≠ BitVec.ofNat 64 (Spike.Lib.X64.WakeOD.arW hp i).ctr := by
  have hwf := Spike.Lib.PlaceWX.wf_link_of_placeWX i hp
  have hrt : ∀ w ∈ (Ly).rtWords, ¬ ((Spike.Lib.X64.WakeOD.arW hp i).heap ≤ w.toNat ∧
      w.toNat < (Spike.Lib.X64.WakeOD.arW hp i).heap + 16 * (Spike.Lib.X64.WakeOD.arW hp i).cells) ∧
      w ≠ BitVec.ofNat 64 (Spike.Lib.X64.WakeOD.arW hp i).ctr := fun w hw => by
    have hm := ((Ly).words_mapped w hw).2.2 0 (by decide)
    obtain ⟨-, -, -, hdh, -, -, -, -, hph, -⟩ := (show (Ly).Λ.WF from hwf).disjoint
    have hs : 16 * Scc.Cert.PlaceOK.allocCells ≤ (Ly).Λ.heap.size :=
      Spike.Lib.X64.Rt.ArenaW.PlaceWX.heapSize_of_placeWX (Spike.Lib.PlaceWX.link i hp)
    have hsep : Scc.Cert.Rt.X64.WordSep w (BitVec.ofNat 64 (Scc.Cert.PlaceOK.heapUseOf (Ly).Λ)) :=
      Scc.Cert.Rt.X64.ctrSep_of_rtWordsOk (Spike.Lib.PlaceWX.rtWordsOk_link_of_placeWX i hp) w hw
    have hh : (Spike.Lib.X64.WakeOD.arW hp i).heap = (Ly).Λ.heap.lo := rfl
    have hc : (Spike.Lib.X64.WakeOD.arW hp i).cells = Scc.Cert.PlaceOK.allocCells := rfl
    have hu : (Spike.Lib.X64.WakeOD.arW hp i).ctr = Scc.Cert.PlaceOK.heapUseOf (Ly).Λ := rfl
    simp only [Scc.Sem.Range.contains, Scc.Sem.Range.Disjoint, Scc.Cert.Rt.X64.WordSep] at hm hdh hph hsep
    refine ⟨by rw [hh, hc]; omega, fun he => ?_⟩
    rw [hu] at he; subst he
    omega
  intro w' hw'
  rcases hw' with rfl | rfl | rfl | rfl | rfl
  · exact hrt _ (Ly).pn_mem
  · exact hrt _ (Ly).lock_mem
  · exact hrt _ (Ly).freeN_mem
  · exact hrt _ (Ly).next_mem
  · obtain ⟨h1, h2⟩ := Spike.Lib.X64.WakePh.CalWf.hoffN_W hp i hA13
    exact ⟨h1, fun he => h2 (by rw [he]; rfl)⟩

/-- **At a box call the header offset fits the cell** (`arOf`'s offset is
one header word, its units positive). -/
theorem hoffQ_R (E : Entry) :
    ∀ q : Call, q.OKB (MR) (Ly).lab → (MR).off q.n q.τ ≤ 16 * (MR).units q.n q.τ := fun q hq => by
  obtain ⟨us, hus⟩ := hq.toS.accs
  rw [hq.one]
  show (Spike.Lib.X64.Rt.arOf (Ly).Λ).off 1 q.τ ≤ 16 * (Spike.Lib.X64.Rt.arOf (Ly).Λ).units 1 q.τ
  simp only [Spike.Lib.X64.Rt.arOf, Arena.ofWords, hus, Nat.mul_zero]
  split <;> omega

set_option maxHeartbeats 1600000 in
/-- **`hWp`'s top case at the root, inside `WSX`**: `wcPreW_WSOg` at the
first stack's top inside `NoSetFsW`; the nodes' `SFactsSt2` at `ownGXW`
by `ownGXW`'s producers, the counter's context by `Land.hctx_R`, the
placement by `WcPl.hplP_W`, the allocator's `X0` by `allocW_free`. -/
theorem hTopP_R (hpo : o.prog = wakeCells) (hlo : (Ly).Λ.code.lo = lo) (hc : Spike.Lib.X64.Rt.CtrZ o)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    {Dt Cl : State → Prop} {frM : TermRun.Frame} {ax : Int64}
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hax : ax.toBitVec.toNat = ((Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    (hc0 : (∀ a, c0.term ≠ .ret a) ∧ Spike.Lib.X64.WakeWf.RunWf wakeSrc c0 [])
    (hpl0 : ∀ s, Spike.Lib.X64ConsumerS.PlacedSE (Ly).Λ (L0T (Ly).Λ) s c0 [])
    (E : Entry) (m0 : MachineData) (σC : Spike.Lib.X64.AS) :
    WcPreW (Spike.Lib.X64.NoSetFsW (tpG (TV) (WSR)) (KW)) (KW) (Ly).exe (Ly).endPc (wR (RS wcLsw (TOP)) wcD)
      (wF (RS wcLsw (TOP)) wcD (FS (Ly) (RS0) wcLsw 0#64 (TOP)) m0 σC) (MR) ((JW) σC) ((JW) σC) := by
  -- the layout's facts
  haveI := (Ly).valid
  have hprog : (Ly).prog = wakeCells := hpo
  have hpS : Scc.Cert.Rt.X64.Lays (Ly).exe wakeCells (Ly).pfx := hprog ▸ (Ly).lays
  have hendS : (Ly).endPc = Scc.Cert.Rt.X64.endOf (Ly).exe wakeCells (Ly).pfx := by
    show Scc.Cert.Rt.X64.endOf (Ly).exe (Ly).prog (Ly).pfx = _; rw [hprog]
  have hwf := Spike.Lib.PlaceWX.wf_link_of_placeWX i hp
  have hwf' : (Ly).Λ.WF := hwf
  have hlab : ∀ l x, codeLabel lo wakeCells l = some x → (Ly).lab l = Int64.ofNat x :=
    fun l x h => Spike.Lib.PlaceWX.hlab_ofPlaceWX hp i l x (by rw [hlo, hpo]; exact h)
  have hΛ : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName :=
    Spike.Lib.PlaceWX.abortLbl_of_placeWX (Spike.Lib.PlaceWX.link i hp)
  have hsite := Spike.Lib.PlaceWX.site_ofPlaceWX hp i
  have hX0 := Spike.Lib.X64.WakePh.StartGlue.x0W_of_freeN hlab hax
  have hsep := Spike.Lib.X64.WakePh.tcbSep_W hp i
  have ha := Spike.Lib.X64.WakePh.tcbM_ne_ntA_W hp i hA13
  have hW := Spike.Lib.X64.WakePh.tcb2_notG_W hp i hA13
  -- the region
  obtain ⟨hR, -⟩ := top_ok (Ly) hwf' m0 σC
  have hR8 := top_al (Ly)
  have hb := top_band (Ly)
  obtain ⟨hRA, hRA8⟩ := Spike.Lib.X64.WakePh.WcW.wAR_ok hR hR8 (by show -wcD ≤ -240; decide)
    (by show (8 : Int) ≤ 8; decide)
  -- the arena
  have hL := Spike.Lib.PlaceWX.link i hp
  obtain ⟨hc1, hc2, -⟩ := Spike.Lib.X64.Rt.ArenaW.ctr_item_of_placeW hL hc
  have hc1' : (Ly).Λ.data.lo ≤ Scc.Cert.PlaceOK.heapUseOf (Ly).Λ := hc1
  have hc2' : Scc.Cert.PlaceOK.heapUseOf (Ly).Λ + 8 ≤ (Ly).Λ.data.lo + (Ly).Λ.data.size := hc2
  have hdb : (Ly).Λ.data.lo + (Ly).Λ.data.size ≤ 2 ^ 32 := Spike.Lib.X64.Rt.ArenaW.data_below_of_placeW hL
  have hsz : 16 * Scc.Cert.PlaceOK.allocCells ≤ (Ly).Λ.heap.size :=
    Spike.Lib.X64.Rt.ArenaW.PlaceWX.heapSize_of_placeWX hL
  have hhb : (Ly).Λ.heap.lo + (Ly).Λ.heap.size ≤ 2 ^ 32 := Spike.Lib.X64.Rt.ArenaW.heap_below_of_placeW hL
  have hh : (MR).heap = (Ly).Λ.heap.lo := rfl
  have hcl' : (MR).cells = Scc.Cert.PlaceOK.allocCells := rfl
  have hct : (MR).ctr = Scc.Cert.PlaceOK.heapUseOf (Ly).Λ := rfl
  have hA : Scc.Cert.PlaceOK.allocCells = 4194304 := rfl
  have hoffQ := hoffQ_R asm hp i ls0 E
  -- the thread pointer's limit word
  have hmr : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 (Ly).Λ) false
      ⟨Spike.Lib.X64.Flow.Ret0.limA (TV), 8⟩ = true := by
    (try simp only [tcbS]); rw [Spike.Lib.X64.Rt.pinA_lab0, Spike.Lib.X64.Rt.limA_tcb0]
    exact ((Ly).words_mapped _ ((Ly).fld_mem (by decide))).2.1
  have hun : ∀ m, wF (RS wcLsw (TOP)) wcD (FS (Ly) (RS0) wcLsw 0#64 (TOP)) m0 σC m →
      Mem.loadInt m.dmem (Spike.Lib.X64.Flow.Ret0.limA (TV)) 8 = none := by
    intro m hm
    (try simp only [tcbS]); rw [Spike.Lib.X64.Rt.pinA_lab0, Spike.Lib.X64.Rt.limA_tcb0]
    exact hm.1.1.1 _ fun j hj => (((Ly).words_mapped _ ((Ly).fld_mem (by decide))).2.2 j hj).elim
      (fun h => .inr (.inl h)) (fun h => .inr (.inr h))
  -- the counter and the headers
  have hmem := Spike.Lib.X64.WakePh.StartGlue.hmemB_of_wordsNone
    (F := wF (RS wcLsw (TOP)) wcD (FS (Ly) (RS0) wcLsw 0#64 (TOP)) m0 σC) (ms := MR) (lab := (Ly).lab) hwf'
    (fun m h => h.1.1.1.wn) (by rw [hh]; exact Nat.le_refl _) (by rw [hh, hcl']; omega)
    (.inr (by rw [hct]; unfold Spike.Lib.DmemPriv.WordIn Scc.Sem.Range.contains; omega)) hoffQ
  have hhdr : ∀ q : Call, q.OKB (MR) (Ly).lab → ∀ o', o' + (MR).units q.n q.τ ≤ (MR).cells →
      (Ly).Λ.heap.lo ≤ q.hdrAt (MR) o' ∧ q.hdrAt (MR) o' + 8 ≤ (Ly).Λ.heap.lo + 16 * Scc.Cert.PlaceOK.allocCells := by
    intro q hq o' ho
    have h1 := hoffQ q hq
    rw [hq.toS.off] at h1
    rw [hcl'] at ho
    rw [Spike.Lib.X64.Alloc.Call.hdrAt, hh]
    generalize q.n * (Spike.Lib.X64.Alloc.mOf q.h).toNat = k at h1 ⊢
    generalize (MR).units q.n q.τ = u at h1 ho
    omega
  have hno : ∀ q : Call, q.OKB (MR) (Ly).lab → ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 (MR).ctr ∨ ∃ o', o' + (MR).units q.n q.τ ≤ (MR).cells ∧ w.toNat = q.hdrAt (MR) o') →
      ∀ j v, (⟨w, 8⟩, v) ∉ Spike.Lib.X64.WakePh.ownW (Ly) (ntA (Ly).lab) j := by
    intro q hq w hw
    refine not_ownW (heap := (MR).heap) (cells := (MR).cells) (ctr := (MR).ctr)
      (fun w' hw' => offW_own hp i hA13 w' hw') ?_
    rcases hw with h | ⟨o', ho, h⟩
    · exact .inl h
    · refine .inr ?_
      have := hhdr q hq o' ho
      rw [hh, hcl', h]
      omega
  have hnoM : ∀ q : Call, q.OKB (MR) (Ly).lab → ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 (MR).ctr ∨ ∃ o', o' + (MR).units q.n q.τ ≤ (MR).cells ∧ w.toNat = q.hdrAt (MR) o') →
      w ≠ Spike.Lib.X64.WakePh.tcbM (Ly) := by
    intro q hq w hw
    rcases hw with rfl | ⟨o', ho, h⟩
    · intro he
      have hsep' : Scc.Cert.Rt.X64.WordSep (Spike.Lib.X64.WakePh.tcbM (Ly))
          (BitVec.ofNat 64 (Scc.Cert.PlaceOK.heapUseOf (Ly).Λ)) :=
        Scc.Cert.Rt.X64.ctrSep_of_rtWordsOk (Spike.Lib.PlaceWX.rtWordsOk_link_of_placeWX i hp) _
          ((Ly).fld_mem (i := 0) (by decide))
      rw [← he, hct] at hsep'
      unfold Scc.Cert.Rt.X64.WordSep at hsep'
      omega
    · have := hhdr q hq o' ho
      have hn := Spike.Lib.X64.WakePh.ne_tcbM_of_heap (L := Ly) hwf' (c := w.toNat) w.isLt
        (by simp only [Scc.Sem.Range.contains]; rw [h]; omega)
      simpa using hn
  -- the nodes' `SFactsSt2` at `ownGXW`
  have hbW : Spike.Lib.X64.WakePh.BandOnP (Ly) (wR (RS wcLsw (TOP)) wcD) (-80) 8 :=
    Spike.Lib.X64.WakePh.OwnMid.bandOnP_mono hb (by decide) (by decide)
  have hS : WcPreW (fun s _ => Spike.Lib.X64ConsumerA.SFactsSt2 (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly))
      (Spike.Lib.X64.WakePh.ownGXW (Ly) (ntA (Ly).lab)) s) (KW) (Ly).exe (Ly).endPc (wR (RS wcLsw (TOP)) wcD)
      (wF (RS wcLsw (TOP)) wcD (FS (Ly) (RS0) wcLsw 0#64 (TOP)) m0 σC) (MR) ((JW) σC) ((JW) σC) :=
    ⟨Spike.Lib.X64.WakePh.OwnWc.proW_wcGX (Λ := (Ly).Λ) hprog hlo hΛ hlab hsite hsep ha hW hbW hR
        (by show -wcD ≤ -72; decide) (by show (0 : Int) ≤ 8; decide)
        (fun _ _ h => Spike.Lib.X64.WakePh.WcPl.tp_wJ0 h) hmr hun,
      Spike.Lib.X64.WakePh.OwnWc.eW_wcGX (Λ := (Ly).Λ) hprog hlo hΛ hlab hsite hsep ha hW hbW hR
        (by show -wcD ≤ -240; decide) (by show (8 : Int) ≤ 8; decide),
      fun q hq hra => Spike.Lib.X64.WakePh.OwnAlloc.allocW_wcGX (Λ := (Ly).Λ) hprog hlab hsite hsep ha hW
        (top_bandA (Ly)) hlo hΛ hRA hRA8 (by show (-160 : Int) ≤ -160; decide) (by show (8 : Int) ≤ 8; decide)
        (by show (-160 : Int) % 8 = 0; decide) (by show (8 : Int) % 8 = 0; decide)
        (by have := (Ly).pool_fit; omega) hra (fun _ _ => hq.toS) (fun _ h => h.1)
        (fun w hw m hm => hmem q hq w hw m hm.1) (hno q hq) (hnoM q hq)⟩
  refine Spike.Lib.X64.Flow.WakeWc.WcPreW.noSetFs hpS hendS
    (wcPreW_WSOg (own := Spike.Lib.X64.WakePh.ownGXW (Ly) (ntA (Ly).lab)) hprog hlo hΛ hlab hsite hcl hX0
      hR hR8 (by show -wcD ≤ -240; decide) (by show (8 : Int) ≤ 8; decide)
      (fun _ _ h => Spike.Lib.X64.WakePh.WcPl.tp_wJ0 h) hun hmem
      (fun _ _ h => by rw [Spike.Lib.X64.WakePh.WcPl.c0_wJ0 h]; exact hc0) hS
      (Spike.Lib.X64.WakePh.WcPl.hplP_W hpl0 σC)
      (fun _ _ _ => Spike.Lib.X64.AllocG.AllocW.imp (allocW_free hlab) (Spike.Lib.X64.Alloc.AllocW.triv _ _)
        (fun s _ h _ => hX0 s h))
      (Spike.Lib.X64.WakePh.Land.hctx_R asm hp i c0 ls0 hc E rfl (TOP) m0 σC) rfl rfl (fun _ _ => rfl) id
      (Spike.Lib.X64.WakePh.Land.hlt_R hp i hc) (by show Scc.Cert.PlaceOK.heapUseOf (Ly).Λ < 2 ^ 64; omega))

/-- **`hWp` at the root, inside `WSX`, at every base** (`hWp_W` from
`hTopP_R`). -/
theorem hWp_R (hpo : o.prog = wakeCells) (hlo : (Ly).Λ.code.lo = lo) (hc : Spike.Lib.X64.Rt.CtrZ o)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    {Dt Cl : State → Prop} {frM : TermRun.Frame} {ax : Int64}
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hax : ax.toBitVec.toNat = ((Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    (hc0 : (∀ a, c0.term ≠ .ret a) ∧ Spike.Lib.X64.WakeWf.RunWf wakeSrc c0 [])
    (hpl0 : ∀ s, Spike.Lib.X64ConsumerS.PlacedSE (Ly).Λ (L0T (Ly).Λ) s c0 []) (E : Entry) :
    ∀ v m0 σC, WcPreW (Spike.Lib.X64.NoSetFsW (tpG (TV) (WSR)) (KW)) (KW) (Ly).exe (Ly).endPc
      (wR (RS wcLsw v) wcD) (wF (RS wcLsw v) wcD (FS (Ly) (RS0) wcLsw 0#64 v) m0 σC) (MR) ((JW) σC) ((JW) σC) :=
  hWp_W (J := JW) (hTopP_R asm hp i c0 ls0 hpo hlo hc hA13 hcl hax hc0 hpl0 E)

end Spike.Lib.X64.WakePh.WcWfR

/-! ## Axioms -/

/-- info: 'Spike.Lib.X64.WakePh.WcWfR.offW_own' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcWfR.offW_own

/-- info: 'Spike.Lib.X64.WakePh.WcWfR.hTopP_R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcWfR.hTopP_R

/-- info: 'Spike.Lib.X64.WakePh.WcWfR.hWp_R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcWfR.hWp_R
