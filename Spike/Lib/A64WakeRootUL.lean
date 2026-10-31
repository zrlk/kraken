/-
**`RootOpen` at `CtxR` with the child's stack unmapped** (wake.w, AArch64):
`CtxRU := CtxR ∧ U r1Of`, so the box store's landing gets the child's stack
unmapped from the context itself (no `hUn1`). `hctr0` is `WakeCtr.hctr0_ofT` as
in `Land.hctr0_R`, its tail `HLandU` (`HLand` with `U r1Of` at `n4`), moved
by `inv0_down`/`inv0_up`.

- `SegInvS.keepUn`: an explicit-invariant segment carries `U r`.
- `w0_mono`: `W0` is monotone in its context.
- `takeU`: `W0W`'s outside moves keep `r1Of` unmapped.
- `inv0_down`, `inv0_up`: `inv0R` at `CtxRU` and at `CtxR`.
- `HLandU`: the counter add's tail with `r1Of` unmapped.
- `hst0_U`, `rootOpen_U`: `hst0` and `RootOpen` at `CtxRU`.
-/
import Spike.Lib.A64WakeLand2
import Spike.Lib.A64WakeStartH0U

namespace Spike.Lib.A64.WakePh.RootUL

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Entry Range)
open Scc.Sem.A64 (textProgram abi)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64ConsumerA (SegInvS TakeCKS)
open Spike.Lib.A64.WakePh.MainGlue (FS)
open Spike.Lib.A64.Flow (swR)
open Spike.Lib.A64.Flow.WakeM (wR wF)
open Spike.Lib.A64.KeepUn (U unXa out_un exec_un)
open Spike.Lib (FragS MemSide SegWS)
open Spike.Lib.WakeOPremW (W0W)
open Spike.Lib.WakeH1Inv (segInvS_weakW)

/-- **An explicit-invariant segment carries `U r`** (`SegW.keepUn`'s rows
at frames): under `ms` with `U r` at its pairs, given outside moves keeping it. -/
theorem SegInvS.keepUn {W inv : FragS isaLSE2} {K : State → State → Prop} {p : Prog} {lbl : Lbl}
    {ms : List TermRun.Frame → MemSide isaLSE2} {r : Range} (hK : ∀ fs, (ms fs).K = some abi)
    (h : SegInvS W K p lbl ms inv) (hKu : ∀ s c fs, W s c fs → ∀ s', K s s' → U r s → U r s') :
    SegInvS (fun s c fs => W s c fs ∧ U r s) K p lbl ms (fun s c fs => inv s c fs ∧ U r s) := by
  rintro s c fs ⟨hi, hu⟩
  obtain ⟨hw, ho, hk⟩ := h s c fs hi
  refine ⟨⟨hw, hu⟩, fun hn => ?_, fun s' hks => ?_⟩
  · cases ho hn with
    | pre c₁ fs₁ hr h =>
      exact .pre c₁ fs₁ hr ((out_un (hK fs₁) hu (Spike.Lib.A64ConsumerA.Out.mono_xa (ms' := unXa (ms fs₁) r) h rfl
        fun _ _ _ _ _ h _ => h)).mono fun _ _ ⟨⟨c₂, fs₂, hr₂, hi⟩, hu⟩ => ⟨c₂, fs₂, hr₂, hi, hu⟩)
    | frame s' c' fs' he hr hx =>
      obtain ⟨c₂, fs₂, hr₂, hi⟩ := hx
      exact .frame s' c' fs' he hr ⟨c₂, fs₂, hr₂, hi, exec_un hu he⟩
  · obtain ⟨c', fs', hr, hx⟩ := hk s' hks
    exact ⟨c', fs', hr, hx, hKu s c fs hw s' hks hu⟩

/-- **`W0` is monotone in its context** (`Ctx` occurs in `ArenaWr`'s second
disjunct and the counter's `WrAt → Ctx`, both positively). -/
theorem w0_mono {Λ μ own ar p Dt Ab Cl Ac L0 ls0 frM X0} {Ctx Ctx' : FragS isaLSE2} {s : State} {c fs}
    (h : Spike.Lib.A64.WakeWf.W0 Λ μ own ar p Dt Ab Cl Ac Ctx L0 ls0 frM X0 s c fs)
    (hC : Ctx s c fs → Ctx' s c fs) : Spike.Lib.A64.WakeWf.W0 Λ μ own ar p Dt Ab Cl Ac Ctx' L0 ls0 frM X0 s c fs :=
  let ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  ⟨h1, h2, h3, h4, h5, h6, h7, h8, fun c' fs' hr L hw hne => (h9 c' fs' hr L hw hne).imp_right
    fun ⟨hc, hn⟩ => ⟨hC hc, hn⟩, fun hw => hC (h10 hw), h11, h12⟩

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (ls0 : Entry → Lsize) (frM : Entry → TermRun.Frame)

set_option hygiene false in
local notation "IW" => Spike.Lib.WakeImmsC0.immsW2 Λ0 SccCode.wakeImms

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hp IW

set_option hygiene false in
local notation "R1" => Spike.Lib.A64.Rt.PreChild.r1Of (Ly).lab

/-- **The root's context with the child's stack unmapped.** -/
def CtxRU (E : Entry) : FragS isaLSE2 := fun s c fs => Land.CtxR hp IW ls0 E s c fs ∧ U R1 s

/-- **`W0W`'s outside moves keep `r1Of` unmapped**: the take of `r0Of`
(`X0W`), disjoint from it; a `clone` refusal sets registers only. -/
theorem takeU (E : Entry) (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true) (Cx : FragS isaLSE2) :
    ∀ s c fs, W0W hp IW E Spike.Lib.A64.WakeWf.DtW Cx (ls0 E) (frM E) s c fs → ∀ s',
      TakeCKS (Spike.Lib.WakeOSide.aW hp IW E) (Spike.Lib.WakeOD.ClW hp IW) s s' → U R1 s → U R1 s' := by
  obtain ⟨-, -, -, -, hd, hw0, hw1⟩ :=
    Spike.Lib.WakeOSide.ranges_W hp IW (Spike.Lib.A64.WakePh.StartPlaceLy.hsub1_W hp IW hA13)
  rintro s c fs hW s' (⟨ha, pm, rfl⟩ | ⟨-, r, -, rfl⟩) hu
  · have hX : Spike.Lib.A64.WakeWf.X0W (Ly) (Spike.Lib.WakeOSide.aW hp IW E) s := hW.2.1
    rw [(hX.2 (congrArg (fun x : Int64 => x.toBitVec.toNat) ha)).1]
    exact Spike.Lib.A64.KeepUn.take_un pm hd hw1 hw0 hu
  · exact hu

set_option hygiene false in
local notation "I0" => Spike.Lib.WakeRoot.inv0R hp IW ls0

/-- **`inv0R` at `CtxRU` is at `CtxR`** (`w0_mono`; `msBot` reads `Ctx` only
through `W1`, which drops it). -/
theorem inv0_down (E : Entry) : ∀ s c fs, I0 (CtxRU hp ls0) frM E s c fs → I0 (Land.CtxR hp IW ls0) frM E s c fs :=
  fun _ _ _ ⟨inv, h, hi⟩ => ⟨inv, segInvS_weakW h fun _ _ _ h => w0_mono h (·.1), hi⟩

/-- **`inv0R` at `CtxR` with `r1Of` unmapped is at `CtxRU`** (`keepUn` on
`GfpS`, `takeU`). -/
theorem inv0_up (E : Entry) (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true) :
    ∀ s c fs, I0 (Land.CtxR hp IW ls0) frM E s c fs → U R1 s → I0 (CtxRU hp ls0) frM E s c fs :=
  fun s c fs hi hu => A64GfpS.le_gfpS (segInvS_weakW (SegInvS.keepUn (fun _ => rfl) A64GfpS.segInvS_gfpS
    (takeU hp ls0 frM E hA13 _)) fun _ _ _ h => w0_mono h.1 fun hc => ⟨hc, h.2⟩) s c fs ⟨hi, hu⟩

/-- **`hst0` at `CtxRU`** from `hst0` at `CtxR`: its witness with `U r1Of`
(`keepUn`), true at the loaded thread. -/
theorem hst0_U (E : Entry) (hE : E.Ok (Ly).Λ) (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    (hst0 : SegWS (W0W hp IW E Spike.Lib.A64.WakeWf.DtW (Land.CtxR hp IW ls0 E) (ls0 E) (frM E))
      (TakeCKS (Spike.Lib.WakeOSide.aW hp IW E) (Spike.Lib.WakeOD.ClW hp IW)) Spike.Lib.WakeT1.wakeSrc
      (Spike.Lib.WakeLoadT.L0T (Ly).Λ) (Spike.Lib.WakeRoot.msBot hp IW ls0 (Land.CtxR hp IW ls0) E)
      (Spike.Lib.WakeRoot.StartP hp IW E) (fun _ _ _ => False)) :
    SegWS (W0W hp IW E Spike.Lib.A64.WakeWf.DtW (CtxRU hp ls0 E) (ls0 E) (frM E))
      (TakeCKS (Spike.Lib.WakeOSide.aW hp IW E) (Spike.Lib.WakeOD.ClW hp IW)) Spike.Lib.WakeT1.wakeSrc
      (Spike.Lib.WakeLoadT.L0T (Ly).Λ) (Spike.Lib.WakeRoot.msBot hp IW ls0 (CtxRU hp ls0) E)
      (Spike.Lib.WakeRoot.StartP hp IW E) (fun _ _ _ => False) := by
  have hsub1 := Spike.Lib.A64.WakePh.StartPlaceLy.hsub1_W hp IW hA13
  obtain ⟨-, -, -, -, -, -, hw1⟩ := Spike.Lib.WakeOSide.ranges_W hp IW hsub1
  obtain ⟨inv, hP, hS⟩ := SegInvS.ofSegWS hst0
  have hS' := segInvS_weakW (SegInvS.keepUn (fun _ => rfl) hS (takeU hp ls0 frM E hA13 _))
    (W := W0W hp IW E Spike.Lib.A64.WakeWf.DtW (CtxRU hp ls0 E) (ls0 E) (frM E))
    fun _ _ _ h => w0_mono h.1 fun hc => ⟨hc, h.2⟩
  refine ⟨fun s c fs => inv s c fs ∧ U R1 s, fun s c fs hp => ⟨hP s c fs hp, ?_⟩, fun s c fs hi => (hS' s c fs hi).1,
    fun s c fs hi => ⟨fun hk => ((hS' s c fs hi).2.1 hk).mono fun _ _ _ h => h.mono fun _ _ _ => .inl,
      (hS' s c fs hi).2.2.mono fun _ _ _ => .inl⟩⟩
  obtain ⟨rfl, -, -⟩ := hp
  exact ⟨Scc.Cert.WideA64.wideSt_threadAt (PlaceW.wideIn_of_placeW hp) E _ _,
    Spike.Lib.WakeOHinit.unowned_stack hp IW hE.1 hsub1 hw1 _ rfl⟩

/-- **The counter add's tail with `r1Of` unmapped**: `Land.HLand` but for
`U r1Of` at the `n4` state (kept from `CtxRU` by the add). -/
def HLandU (E : Entry) : Prop :=
  ∀ (ms0 : MemSide isaLSE2) R F q, ms0 = { Land.refW hp IW ls0 E with xa := ms0.xa } → Land.GcW hp IW E ms0 R F q →
    Spike.Lib.A64.WakeCtr.CtrOk ms0 (Ly).lab R F q →
    ∀ s c, Spike.Lib.A64.Flow.At (Ly).exe (Ly).endPc R F (Spike.Lib.A64.Alloc.N (Ly).lab ms0 q .n4) s c →
      Spike.Lib.A64.KeepTP.TP (UInt64.ofBitVec (Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64)) s → U R1 s →
      I0 (Land.CtxR hp IW ls0) frM E s c []

/-- **`RootOpen` at `CtxRU`** (at `IW`): `hst0` by `hst0_U`; `hctr0` by
`WakeCtr.hctr0_ofT` (as `Land.hctr0_R`) at `inv0 := U r1Of → inv0R`, its
landing's `inv0R` moved up by `inv0_up` with `U r1Of` kept by the add
(`exec_un`); `hnew0` as
`WakeCtr.hnew0_of`, the landing a `Box` (`Hxa.box_landing`) with `U r1Of`
kept by the store (no `hUn1`). Open: `hst0` at `CtxR`'s
premises, `hland`, `h1`/`hF0`. -/
theorem rootOpen_U (E : Entry) (hE : E.Ok (Ly).Λ)
    (hpa : textProgram SccCertificate.asm = .ok o.prog) (hwp : textProgram SccCertificate.asm = .ok wakeProg)
    (hc : Spike.Lib.A64.Rt.CtrZ o) (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    (hst0 : SegWS (W0W hp IW E Spike.Lib.A64.WakeWf.DtW (Land.CtxR hp IW ls0 E) (ls0 E) (frM E))
      (TakeCKS (Spike.Lib.WakeOSide.aW hp IW E) (Spike.Lib.WakeOD.ClW hp IW)) Spike.Lib.WakeT1.wakeSrc
      (Spike.Lib.WakeLoadT.L0T (Ly).Λ) (Spike.Lib.WakeRoot.msBot hp IW ls0 (Land.CtxR hp IW ls0) E)
      (Spike.Lib.WakeRoot.StartP hp IW E) (fun _ _ _ => False))
    (hland : HLandU hp ls0 frM E) {F0 : MachineData → Prop}
    (h1 : Spike.Lib.WakeRoot.H1R hp IW ls0 (CtxRU hp ls0)
      (Spike.Lib.WakeRoot.msBot hp IW ls0 (CtxRU hp ls0) E []) F0 E)
    (hF0 : ∀ v m0 σC m, wF (swR v (-384) 0) 336 (FS (Ly) (Spike.Lib.A64.Rt.rS0 (Ly)) 384 0#64 v) m0 σC m → F0 m) :
    Spike.Lib.WakeRoot.RootOpen hp IW ls0 (CtxRU hp ls0) frM E where
  hst0 := hst0_U hp ls0 frM E hE hA13 hst0
  hctr0 := by
    intro s c fs hi hC hW c' fs' hr ha
    obtain ⟨k, op, g, x, τ, e, n, h1, h2, h3, h4, h5, h6, h7⟩ :=
      Spike.Lib.A64.WakeCtr.hctr0_ofT (inv0 := fun s c fs => U R1 s → I0 (Land.CtxR hp IW ls0) frM E s c fs)
        (Land.hcode_R hp IW hpa hwp) (Spike.Lib.A64.WakeCtr.stAt_noWr (Land.hlt_R hp IW ls0 hc E)
          (Spike.Lib.WakeOD.hok_W hp IW E (Spike.Lib.WakeHG.cTW hp IW) Spike.Lib.A64.WakeWf.DtW (ls0 E)
            (fun _ _ _ => False) (fun _ _ _ => False) (fun _ _ _ _ _ _ => False) (fun _ _ _ _ _ _ => False) hc).ctr_lt)
        (fun ms0 R F q hms hG hok s c hj htp hu => hland ms0 R F q hms hG hok s c hj htp hu)
        s c fs (fun _ => inv0_down hp ls0 frM E s c fs hi) hC.1 hW c' fs' hr ha
    refine ⟨k, op, g, x, τ, e, n, h1, h2, h3, h4, h5, h6, fun old hG hown hle hlo => ?_⟩
    obtain ⟨hG', hP, c2, fs2, hr2, hI⟩ := h7 old hG hown hle hlo
    have hU : U R1 (g old) := exec_un hC.2 h1 old
    exact ⟨hG', hP, c2, fs2, hr2, hI.imp (fun ⟨h1, h2, h3⟩ => ⟨h1, h2, inv0_up hp ls0 frM E hA13 _ _ _ (h3 hU) hU⟩) id⟩
  hnew0 := by
    intro s c fs _ hC hW c' fs' hr _ _ _ _
    obtain ⟨rfl, Lnd, hG, kr, A, V, s', x, a, ty, e, w, wold, old, hN, hex, hmp, ht, hev, hacc, hv, hh, hold, hA,
      hcl, hX⟩ := hC.1.resolve_left fun h =>
        hW (Spike.Lib.A64.WakeCtr.ctrAt_wr (Land.hcode_R hp IW hpa hwp) rfl s c fs h.1)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Spike.Lib.FrameNew.FrameRun.eq_of_new hr ht.choose_spec)
    have hU : U R1 s' := exec_un hC.2 hex true
    refine ⟨kr, A, V, s', x, a, ty, e, w, wold, old, hN, hex, hmp, ht, hev, hacc, hv, hh, hold, hA, hcl,
      fun l hl => ?_⟩
    obtain ⟨v, m0, σC, rfl⟩ := hG
    obtain ⟨-, hAt, htp⟩ := hX l hl
    have hA' := Land.at_bX_xa (ms' := Spike.Lib.WakeRoot.msBot hp IW ls0 (CtxRU hp ls0) E []) rfl hAt
    have hB := Hxa.box_landing hp ls0 (CtxRU hp ls0) E hA13 hF0 hA' htp hU
    obtain ⟨-, -, -, -, -, -, -, q, -, -, -, ob, hAo, hlt⟩ := hA'
    have hf : (Spike.Lib.WakeRoot.msBot hp IW ls0 (CtxRU hp ls0) E []).off 1 q.1.τ = 8 :=
      Spike.Lib.LowerA64.arOf_off_eq (Λ := (Ly).Λ) q.2.toS.accs
    have hu : 1 ≤ (Spike.Lib.WakeRoot.msBot hp IW ls0 (CtxRU hp ls0) E []).units 1 q.1.τ :=
      Spike.Lib.LowerA64.arOf_units_pos (Λ := (Ly).Λ) q.2.toS.accs
    have hcl2 : 2 ≤ Scc.Cert.PlaceOK.allocCells := by decide
    have hAL : Spike.Lib.HeapLand.AllocLand (Spike.Lib.WakeOD.arW hp IW).heap (Spike.Lib.WakeOD.arW hp IW).cells
        A.toNat 1 := by
      show (Spike.Lib.WakeRoot.msBot hp IW ls0 (CtxRU hp ls0) E []).heap + 8 ≤ A.toNat ∧
        A.toNat + 8 * 1 ≤ (Spike.Lib.WakeRoot.msBot hp IW ls0 (CtxRU hp ls0) E []).heap +
          16 * (Spike.Lib.WakeRoot.msBot hp IW ls0 (CtxRU hp ls0) E []).cells ∧
        1 + 1 ≤ (Spike.Lib.WakeRoot.msBot hp IW ls0 (CtxRU hp ls0) E []).cells
      rw [hf] at hAo; exact ⟨by omega, by omega, hcl2⟩
    exact ⟨hAL, .inr ⟨l, _, 1, hl, hAL, rfl, rfl, (h1 l _ 1 hl hAL).2.1 _ _ hB⟩⟩

/-- **Non-vacuity**: the start pair is in `inv0R` at `CtxRU` (`hst0_U`'s
witness carries `U r1Of`, from `unowned_stack` at the loaded thread). -/
example (E : Entry) (hE : E.Ok (Ly).Λ) (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    (hst0 : SegWS (W0W hp IW E Spike.Lib.A64.WakeWf.DtW (Land.CtxR hp IW ls0 E) (ls0 E) (frM E))
      (TakeCKS (Spike.Lib.WakeOSide.aW hp IW E) (Spike.Lib.WakeOD.ClW hp IW)) Spike.Lib.WakeT1.wakeSrc
      (Spike.Lib.WakeLoadT.L0T (Ly).Λ) (Spike.Lib.WakeRoot.msBot hp IW ls0 (Land.CtxR hp IW ls0) E)
      (Spike.Lib.WakeRoot.StartP hp IW E) (fun _ _ _ => False)) :
    ∀ s c fs, Spike.Lib.WakeRoot.StartP hp IW E s c fs → I0 (CtxRU hp ls0) frM E s c fs :=
  A64GfpS.gfpS_of_segWS (hst0_U hp ls0 frM E hE hA13 hst0)

end Spike.Lib.A64.WakePh.RootUL

/-- info: 'Spike.Lib.A64.WakePh.RootUL.inv0_up' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.RootUL.inv0_up

/-- info: 'Spike.Lib.A64.WakePh.RootUL.hst0_U' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.RootUL.hst0_U

/-- info: 'Spike.Lib.A64.WakePh.RootUL.rootOpen_U' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.RootUL.rootOpen_U
