/-
**`wake_start_wc_h0` at wake's start choices** (AArch64): the start
control `c0 := WakeC0.c0W`, the program `wakeSrc`, the labels
`L0T`/`ls0T`, the dummy heap word `WakeHG.cTW` and the take site
`ax := WakeOSide.aW`, with the leaf premises discharged:

- `hp` by `StartPlaceLy.hp_W`, `hlo` by `hlo_W`;
- `hc0`, `hbx` by `WakeC0.c0W_ctl`, `c0W_box`;
- `hax` by `WakeOSide.aW_site` (with `PlaceW.site_ofPlaceW`);
- `hro` by `WakeOSide.hro_W`, `hfree` by `StartPlaceLy.hfree_W`,
  `hctr2` by `hctr2_of_data`, `hcT` by `hcT_W`, `hrt0` by `StartH0.rt_L0T`;
- `htiW` by `StartH0Ti.htiW_place`.

Left as premises: the loader's facts (`hpa`, `hwp`, `hlo0`, `hstat`, `hA13`,
`hpin2`, `hctrD`, `hc`), the placement `hpl0` and the facts `hC0` at
`c0W`, and `wc_main`'s `hWp`/`hWs`/`hxa`. The site frame `P := Pz rS0`
(`StartH0Ti.pz_fstable_entry`) is a conjunct of the entry's pre.

- `wake_start_wc_h0W`: the statement.
-/
import Spike.Lib.A64WakeStartH0Ti
import Spike.Lib.A64WakeC0
import Spike.Lib.WakeAWSite

namespace Spike.Lib.A64.WakePh.StartH0G

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem.A64 (textProgram)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (RuntimeLayout entryR rtF)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64.WakePh.StartWf (WS)
open Spike.Lib.A64.WakePh.MainGlue (FS JS)
open Spike.Lib.A64.Flow (swR)
open Spike.Lib.A64.Flow.Ret0 (pinA)
open Spike.Lib.A64.Flow.WakeM (wR wF wJ0 wNC)
open Spike.Lib.A64.Flow.WakeWc (WcPreW WcSp0W bX wX)
open Spike.Lib.A64.KeepTP (TP tpXa)
open Spike.Lib.DmemPriv (WordsNone WordsNoneP)
open Spike.Lib (FragS SegW)
open Spike.Lib.A64.WakePh (lo ownG)
open Spike.Lib.WakeLoadT (L0T ls0T)
open Spike.Lib.WakeT1 (wakeSrc)
open Spike.Lib.WakeC0 (c0W)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hpw i

set_option hygiene false in
local notation "AR" => Spike.Lib.WakeOD.arW hpw i

set_option hygiene false in
local notation "NT" => Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab

set_option hygiene false in
local notation "FWN" => fun m : MachineData => WordsNoneP (Ly).Λ m.dmem ∧ rtF (Ly) m

set_option hygiene false in
local notation "RS" => Spike.Lib.A64.Rt.rS0 (Ly)

set_option hygiene false in
/-- The memory side at the start's labels and the dummy heap word. -/
local notation "MS" => Spike.Lib.A64ConsumerA.msOfA (Ly).Λ μ rd (Spike.Lib.WakeOG.gW hpw i (Spike.Lib.WakeHG.cTW hpw i))
  (fun s _ => ownG (Ly) NT s) (AR) I (L0T (Ly).Λ) (ls0T ls) []

set_option hygiene false in
/-- The start's fragment at `wakeSrc`, the clone phase `ClW`, the take site `aW E`. -/
local notation "WSW" => WS (Ly) NT (AR) wakeSrc Dt (Spike.Lib.WakeOD.ClW hpw i) Ctx lbl lsize frM
  (Spike.Lib.A64.WakeWf.X0W (Ly) (Spike.Lib.WakeOSide.aW hpw i E))

set_option hygiene false in
local notation "JW" => fun σC => wJ0 (wNC (Ly).lab (JS (Ly) 0#64 c0W)).J σC

set_option hygiene false in
local notation "TPW" => TP (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))

/-- **From `_start` to `wc_main`'s heap abort at wake's start choices**:
`StartH0.wake_start_wc_h0` at `c0W`, `wakeSrc`, `L0T`/`ls0T`, `cTW`,
`aW E`, its leaf premises discharged from the loader's facts; the site
frame `Pz rS0` beside the entry's frame. -/
theorem wake_start_wc_h0W {E : Scc.Sem.Entry} (hE : E.Ok (Ly).Λ)
    {Dt : State → Prop} {Ctx : FragS isaLSE2} {lbl lbl' : Lbl} {lsize : Lsize} {frM : TermRun.Frame}
    {μ : Scc.Sem.Marks} {rd : TermRun.Word → Prop} {I : Spike.Lib.A64ConsumerS.InvS} {ls : Lsize}
    {pS : Prog} {lblS : Lbl}
    (hpa : textProgram SccCertificate.asm = .ok o.prog) (hwp : textProgram SccCertificate.asm = .ok wakeProg)
    (hlo0 : Λ0.code.lo = lo) (hstat : Λ0.static = fun _ => none)
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (hctrD : ∀ a ∈ [(Ly).pnA, (Ly).lockA, (Ly).freeNA, (Ly).nextA], (Ly).Λ.data.contains a.toNat)
    (hc : Spike.Lib.A64.Rt.CtrZ o)
    /- named premise: `c0W` placed at every state -/
    (hpl0 : ∀ s, Spike.Lib.A64ConsumerS.PlacedSE (Ly).Λ lbl s c0W [])
    /- named premise: the consumer facts at `c0W` -/
    (hC0 : Spike.Lib.A64Consumer.CFacts (Ly).Λ lbl' c0W)
    (hWp : ∀ v m0 σC, WcPreW (Spike.Lib.A64.Flow.NoMsrW (Spike.Lib.A64.Flow.WakeWc.tpG (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64)) (WSW)) (Spike.Lib.A64.PhRec.K (Ly) RS))
      (Spike.Lib.A64.PhRec.K (Ly) RS) (Ly).exe (Ly).endPc (wR (swR v (-384) 0) 336)
      (wF (swR v (-384) 0) 336 (FS (Ly) RS 384 0#64 v) m0 σC)
      (tpXa MS (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) ((JW) σC) ((JW) σC))
    (hWs : ∀ v m0 σC, WcSp0W (Spike.Lib.A64.Flow.NoMsrW (Spike.Lib.A64.Flow.WakeWc.tpG (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64)) (WSW)) (Spike.Lib.A64.PhRec.K (Ly) RS))
      (Spike.Lib.A64.PhRec.K (Ly) RS) (Ly).exe (Ly).endPc (wR (swR v (-384) 0) 336)
      (wF (swR v (-384) 0) 336 (FS (Ly) RS 384 0#64 v) m0 σC)
      (tpXa MS (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) ((JW) σC))
    (hxa : ∀ v m0 σC l A s c, lblS l = none →
      Spike.Lib.A64.Flow.At (Ly).exe (Ly).endPc (wR (swR v (-384) 0) 336)
        (wF (swR v (-384) 0) 336 (FS (Ly) RS 384 0#64 v) m0 σC) (bX MS (Ly).lab ((JW) σC) l A) s c →
      TPW s → (MS).xa l A 1 s c) :
    SegW (WSW) (Spike.Lib.A64.PhRec.K (Ly) RS) pS lblS MS
      (fun s c => Spike.Lib.A64.Flow.At (Ly).exe (Ly).endPc (entryR E) FWN
        (Spike.Lib.A64.Flow.Ret0.entryN (Ly).lab c0W) s c ∧ Spike.Lib.A64Consumer.Pz (Spike.Lib.A64.Rt.rS0 (Ly)) s.st.1)
      (fun s c => ∃ v m0 σC,
        Spike.Lib.A64.Flow.At (Ly).exe (Ly).endPc (wR (swR v (-384) 0) 336)
          (wF (swR v (-384) 0) 336 (FS (Ly) RS 384 0#64 v) m0 σC) (wX MS (Ly).lab ((JW) σC) .abort) s c ∧
        TPW s) := by
  have hp := Spike.Lib.A64.WakePh.StartPlaceLy.hp_W hpa hwp
  have hlo := Spike.Lib.A64.WakePh.StartPlaceLy.hlo_W hpw i hlo0
  have hprog := Spike.Lib.WakeSrcCtl.prog_W hpw i hpa hwp
  have hwpL : textProgram SccCertificate.asm = .ok (Ly).prog := by rw [hprog]; exact hwp
  have hax : (Spike.Lib.WakeOSide.aW hpw i E).toBitVec.toNat =
      ((Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat := by
    rw [Spike.Lib.WakeOSide.aW_site hpw i hpa hwp hwpL (Spike.Lib.PlaceW.site_ofPlaceW hpw i) E]
  have hro := Spike.Lib.WakeOSide.hro_W hpw i
  refine (Spike.Lib.A64.WakePh.StartH0.wake_start_wc_h0 hpw i hE hp hlo Spike.Lib.WakeC0.c0W_ctl hpl0 hax hA13 hro
    hC0 (Spike.Lib.A64.WakePh.StartPlaceLy.hfree_W hpw i hstat ls)
    (Spike.Lib.A64.WakePh.StartPlaceLy.hctr2_of_data hpw i hpin2 hctrD)
    (Spike.Lib.A64.WakePh.StartPlaceLy.hcT_W hpw i) hc hpin2
    (Spike.Lib.A64.WakePh.StartH0.rt_L0T hstat ls) Spike.Lib.WakeC0.c0W_box
    (Spike.Lib.A64.WakePh.StartH0Ti.pz_fstable_entry hE)
    (Spike.Lib.A64.WakePh.StartH0Ti.htiW_place hpw i hE hp hlo Spike.Lib.WakeC0.c0W_ctl hpl0 hax hA13 hro hC0)
    hWp hWs hxa).mono_pre fun _ _ ⟨⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩, hz⟩ => ⟨he, hn, hdc, hpc, σ, hA, ⟨hD, hz⟩, hJ⟩

end Spike.Lib.A64.WakePh.StartH0G

/-- info: 'Spike.Lib.A64.WakePh.StartH0G.wake_start_wc_h0W' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.StartH0G.wake_start_wc_h0W
