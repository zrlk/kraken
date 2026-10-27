/-
**The loaded thread's run at depth inside `SFactsS`** (AArch64, H7a calls;
the twin of `Spike/Lib/LowerX64/StartSegSG.lean`): `a64_start_segWS`
(`Spike/Lib/LowerA64/StartSegS.lean`) with the runtime's obligations from
the call-free ones inside `SFacts … Dt` (`startAllUW_gen`, `swUW_gen_dt`,
`_start`'s block), the user function's interface `UserCallWS` inside
`SFactsS … Dt`, `main`'s exit at the post `UPostS`.

The runtime's obligations hold at every control, but `SFactsS` at a pair
holds only for a `Good1` one (`SFactsS.ofSFacts0`): they are lifted to the
world `Good1 p (c, fs) → SFactsS …` (the `*_wmono` lemmas), where the user
function's interface lies too, and the segment from the entry (whose pair
is `Good1`, `hg0`) keeps its pairs `Good1` (`SegWS.good1`,
`Spike/Lib/SegGood1.lean`), so they carry `SFactsS`.

- `startW_wmono`, `sp0W_wmono`, `sp2W_wmono`, `proW_wmono`, `exitW_wmono`,
  `mainUW_wmono`: `scc_rt_start`'s and `scc_rt_main`'s obligations in a
  larger `W`;
- `segWS_wmono`: a segment at depth inside a larger fragment;
- `a64_start_segWSG`: the run from `_start` one segment at depth inside
  `SFactsS … Dt`, at any callee room `D` of the user `main`.
-/
import Spike.Lib.LowerA64.StartSegS
import Spike.Lib.LowerA64.StartSeg1
import Spike.Lib.LowerA64.UPostS
import Spike.Lib.LowerA64.Correct
import Spike.Lib.A64SFactsS1
import Spike.Lib.SegGood1

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib.A64Consumer (CFacts SFacts Lbl Lsize msOf)
open Spike.Lib.A64ConsumerS (SFactsS)
open Spike.Lib.A64.Rt (RuntimeLayout StartAllUWS SwUW MainUW nilW bareMC rtF entryR)
open Spike.Lib.A64.Rt.StartU (blkW_wmono nodeW_wmono tcbW_wmono tiW_wmono)
open Spike.Lib.A64.Flow.Ret0 (StackM limA Sp0W Sp2W)
open Spike.Lib.A64.PhRec (μ K)

section WMono

variable {W W' : Frag isaLSE2} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64} {R : Region}
  {F : MachineData → Prop}

/-- `scc_rt_start`'s entry obligations in a larger `W`. -/
theorem startW_wmono (hW : ∀ s c, W s c → W' s c) {J : AS → Ctl → Prop} (h : StartW W K exe endPc R F J) :
    StartW W' K exe endPc R F J :=
  ⟨blkW_wmono hW h.w0, nodeW_wmono hW h.w1, nodeW_wmono hW h.w2, blkW_wmono hW h.w3, nodeW_wmono hW h.w4⟩

/-- `scc_rt_start`'s obligations up to `.sp2` in a larger `W`. -/
theorem sp0W_wmono (hW : ∀ s c, W s c → W' s c) {n0 : BitVec 64} {c0 : Ctl} (h : Sp0W W K exe endPc R F n0 c0) :
    Sp0W W' K exe endPc R F n0 c0 :=
  ⟨startW_wmono hW h.start, blkW_wmono hW h.blk, fun g hg i => tcbW_wmono hW (h.tcb g hg i)⟩

/-- `scc_rt_start`'s obligations from `.sp2` to the switch in a larger `W`. -/
theorem sp2W_wmono (hW : ∀ s c, W s c → W' s c) {rS : Scc.Sem.Range} {n0 k0 : BitVec 64} {c0 : Ctl}
    (h : Sp2W W K exe endPc R F rS n0 k0 c0) : Sp2W W' K exe endPc R F rS n0 k0 c0 :=
  ⟨blkW_wmono hW h.b2, fun g hg i => tiW_wmono hW (h.ti g hg i), blkW_wmono hW h.b3, nodeW_wmono hW h.msr⟩

/-- A stack-checked prologue's obligations in a larger `W`. -/
theorem proW_wmono (hW : ∀ s c, W s c → W' s c) {ms : MemSide isaLSE2} {pc0 Z lim : Int64} {L : Label}
    {ps : List (XReg × Int64)} {J : AS → Ctl → Prop} (h : ProW W K exe endPc R F ms pc0 Z lim L ps J) :
    ProW W' K exe endPc R F ms pc0 Z lim L ps J :=
  ⟨blkW_wmono hW h.w0, nodeW_wmono hW h.w1, blkW_wmono hW h.w2, blkW_wmono hW h.w3⟩

/-- An `exit_group` tail's obligations in a larger `W`. -/
theorem exitW_wmono (hW : ∀ s c, W s c → W' s c) {n : ND} {k : Int64} (h : ExitW W K exe endPc R F n k) :
    ExitW W' K exe endPc R F n k :=
  ⟨blkW_wmono hW h.w0, nodeW_wmono hW h.w1⟩

/-- `scc_rt_main`'s own obligations in a larger `W`. -/
theorem mainUW_wmono (hW : ∀ s c, W s c → W' s c) {ms : MemSide isaLSE2} {mc : Spike.Lib.A64.Rt.MainCode}
    {Post : Ctl → BitVec 64 → Prop} {g : Ret0.MainG} (h : MainUW W K exe endPc R F ms mc Post g) :
    MainUW W' K exe endPc R F ms mc Post g :=
  ⟨proW_wmono hW h.pro, blkW_wmono hW h.call, exitW_wmono hW h.exit⟩

end WMono

/-- **A segment at depth inside a larger fragment.** -/
theorem segWS_wmono {I : ISA} {W W' : FragS I} {K : I.State → I.State → Prop} {p : Prog}
    {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide I} {P Q : FragS I}
    (h : SegWS W K p lbl ms P Q) (hW : ∀ s c fs, W s c fs → W' s c fs) : SegWS W' K p lbl ms P Q :=
  let ⟨inv, hP, hiW, hcl⟩ := h
  ⟨inv, hP, fun s c fs h => hW s c fs (hiW s c fs h), hcl⟩

section StartSG

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
  (h : placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option quotPrecheck false

/-- The runtime's layout of the output. -/
local notation "Ly" => RuntimeLayout.ofPlaceOK h i

/-- **The call-free facts of the start's run**: `SFacts` at the record, the
first stack `rS0` taken, the write tail `Dt`. -/
local notation "WS" lbl:max Dt:max => fun s c => SFacts (Ly).Λ (μ (Ly)) (Spike.Lib.A64.PhRec.own (Ly))
  (Spike.Lib.A64.Rt.rS0 (Ly)) (Spike.Lib.A64.PhRec.Tk (Ly)) lbl s c Dt

/-- **The facts at depth of the start's run**: `SFactsS` at the record, the
owned words not depending on the frames. -/
local notation "WSS" p:max lbl:max cl:max ctr:max Dt:max => fun s c fs => SFactsS (Ly).Λ (μ (Ly)) p
  (fun s _ => Spike.Lib.A64.PhRec.own (Ly) s) (Spike.Lib.A64.Rt.rS0 (Ly)) (Spike.Lib.A64.PhRec.Tk (Ly)) lbl cl ctr
  s c fs Dt

/-- The placement's memory side at the record. -/
local notation "MS" rd:max G:max lbl:max lsize:max =>
  msOf (Ly).Λ (μ (Ly)) rd G (Spike.Lib.A64.PhRec.own (Ly)) lbl lsize

set_option maxHeartbeats 800000 in
/-- **The loaded thread's run is one segment at depth inside `SFactsS …
Dt`**, for an `Accepted1` program `p` (`hp`) whose start control is `Good1`
(`hg0`), under memory sides with frames agreeing with the placement's with
no frame (`hms`, `hMs`), a write tail `Dt` whose system calls are no `write`
to the output (`hDt`): `a64_start_segWS`'s premises at the post `UPostS`
(`main`'s exit by `uPostS_exit`) but `hEntry` and `hW`, which come from
`_start`'s block inside `SFacts … Dt` (`hEntry`), `startAllUW_gen` and
`swUW_gen_dt`'s (its user field at a room no region holds) at `c0`'s facts
(`hC0`) and `scc_rt_main`'s phase facts (`hmph`, `hsw`), and the user
function's interface inside `SFactsS … Dt` (`hU`), from the entry frame
condition `FE` (implying `rtF`, stable, kept by the take), whose private
memory's facts `U` (kept in the new stack's region) the interface's frame
condition carries. -/
theorem a64_start_segWSG (hs : o.place.tail = .bare) {p : Prog} (hp : Scc.Lower.Accepted1 p = true)
    (hg0 : Good1 p (Spike.Lib.A64Consumer.c0, []))
    {ms : List TermRun.Frame → MemSide isaLSE2} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {lbl : Lbl}
    {lsize : Lsize} (hms : ms [] = MS rd G lbl lsize) (hMs : MsAgree ms) {Dt : State → Prop}
    (hDt : ∀ s, Dt s → Scc.Sem.A64.abi.atSys s = true → ∀ buf n,
      Scc.Sem.Kernel.decode Scc.Sem.A64.abi.nrs (Scc.Sem.A64.abi.nr s) (Scc.Sem.A64.abi.arg s) ≠
        some (.write 1 buf n))
    {cl ctr : Nat}
    (hfree : Spike.Lib.A64.Rt.RtFree (Ly) lbl lsize)
    {E : Scc.Sem.Entry} (hE : E.Ok (Ly).Λ)
    {D : Int} (hD0 : 0 ≤ D) (hD8 : D % 8 = 0) (hD : D + 48 ≤ 16384) {ZU : Int64}
    (hGh : G ⟨(Ly).pinA + 0#64, 8⟩ ((Ret0.AllocTcb.hdr0 ||| 1#64 <<< 36).setWidth 128))
    (hGf : ∀ e ∈ Ret0.ThreadInit.fields ((Ly).pinA + 0#64 + 8#64) ((Ly).stacksA + 0#64),
      G ⟨(Ly).pinA + 0#64 + 8#64 + BitVec.ofNat 64 e.1, 8⟩ (e.2.setWidth 128))
    (hGt : G ⟨(Ly).pnA, 8⟩ ((0#64 + Ret0.AllocTcb.tcbLen).setWidth 128))
    (hownT : Ret0.OwnAt (MS rd G lbl lsize) (Ly).exe (Ly).endPc (Ret0.AllocTcb.rmwPc (Ly).lab)
      (Ly).pnA 0#64)
    (hG1 : G ⟨(Ly).lockA, 8⟩ ((1#64).setWidth 128)) (hG0 : G ⟨(Ly).lockA, 8⟩ ((0#64).setWidth 128))
    (hGn : G ⟨(Ly).nextA, 8⟩ ((0#64 + Ret0.StackTake.size0).setWidth 128))
    (hownL : Ret0.OwnAt (MS rd G lbl lsize) (Ly).exe (Ly).endPc (Ret0.StackTake.swpPc (Ly).lab)
      (Ly).lockA 0#64)
    (hownF : Ret0.OwnAt (MS rd G lbl lsize) (Ly).exe (Ly).endPc (Ret0.StackTake.freeNPc (Ly).lab)
      (Ly).freeNA 0#64)
    (hownN : Ret0.OwnAt (MS rd G lbl lsize) (Ly).exe (Ly).endPc (Ret0.StackTake.nextPc (Ly).lab)
      (Ly).nextA 0#64)
    (hroomM : ∀ v : Val, G ⟨limA (UInt64.ofBitVec ((Ly).pinA + 0#64 + 8#64)), 8⟩ v →
      (v.setWidth 64).toNat ≤ (Ret0.stacksA (Ly).lab + 0#64 + 16384#64 - bareMC.Z.toBitVec).toNat)
    (hroomU : ∀ v : Val, G ⟨limA (UInt64.ofBitVec ((Ly).pinA + 0#64 + 8#64)), 8⟩ v →
      (v.setWidth 64).toNat ≤ (Ret0.stacksA (Ly).lab + 0#64 + 16384#64 - bareMC.Z.toBitVec - ZU.toBitVec).toNat)
    (hC0 : CFacts (Ly).Λ lbl Spike.Lib.A64Consumer.c0)
    (hmph : Spike.Lib.A64.Rt.MainU.MainPh (Spike.Lib.A64.PhRec.okPc (Ly)) (Spike.Lib.A64.PhRec.ph (Ly)) (Ly).lab
      bareMC)
    (hsw : Spike.Lib.A64.Rt.MainU.SwPh (Spike.Lib.A64.PhRec.okPc (Ly)) (Spike.Lib.A64.PhRec.ph (Ly)) (Ly).lab)
    {FE : MachineData → Prop} (hFE : ∀ m, FE m → rtF (Ly) m) (hFEs : FStable (entryR E) FE)
    (hFEk : ∀ m pm, FE m → FE (Ret0.takeMem pm (Spike.Lib.A64.Rt.rS0 (Ly)) m))
    {U : _root_.Mem 64 → Prop} (hUF : ∀ m, FE m → U m.dmem)
    (hUS : FStable (swR (Ret0.stacksA (Ly).lab + 0#64 + 16384#64) (-(D + 48)) 0) fun m => U m.dmem)
    (hEntry : BlkW (WS lbl Dt) (K (Ly) (Spike.Lib.A64.Rt.rS0 (Ly))) (Ly).exe (Ly).endPc (entryR E) FE
      (Ret0.entryN (Ly).lab Spike.Lib.A64Consumer.c0) Ret0.entryB)
    (hU : ∀ v, Spike.Lib.A64.Rt.UserCallWS (WSS p lbl cl ctr Dt) (K (Ly) (Spike.Lib.A64.Rt.rS0 (Ly))) p lbl ms
      (Ly).exe (Ly).endPc (swR v (-(D + 48)) 0)
      (fun m => Spike.Lib.A64.Rt.swFSL (D + 48) (Spike.Lib.A64.Rt.rS0 (Ly))
        (Ret0.stacksA (Ly).lab + 0#64 + 16384#64) (limA (UInt64.ofBitVec (Ret0.pinA (Ly).lab + 0#64 + 8#64))) v m ∧
        U m.dmem)
      bareMC.fn bareMC.Z D ZU (UPostS p lbl Spike.Lib.A64Consumer.c0) ((Ly).lab bareMC.e0 + 4).toBitVec
      Spike.Lib.A64Consumer.c0 (UInt64.ofBitVec (Ret0.pinA (Ly).lab + 0#64 + 8#64)))
    {Q : FragS isaLSE2} :
    SegWS (WSS p lbl cl ctr Dt) (K (Ly) (Spike.Lib.A64.Rt.rS0 (Ly))) p lbl ms
      ((At (Ly).exe (Ly).endPc (entryR E) FE (Ret0.entryN (Ly).lab Spike.Lib.A64Consumer.c0)).at []) Q := by
  -- the world of the lift: `SFactsS` at the `Good1` pairs
  let W : FragS isaLSE2 := fun s c fs => Good1 p (c, fs) → SFactsS (Ly).Λ (μ (Ly)) p
    (fun s _ => Spike.Lib.A64.PhRec.own (Ly) s) (Spike.Lib.A64.Rt.rS0 (Ly)) (Spike.Lib.A64.PhRec.Tk (Ly)) lbl cl ctr
    s c fs Dt
  have hmap : ∀ s c, (WS lbl Dt) s c → nilW W s c := fun s c hw hg => SFactsS.ofSFacts0 hw hp hg
  have hrc := Spike.Lib.A64.Rt.rtCodeIn_of_ok (rtCodeOk_bare_of_placeOKAt h hs)
  have hsub := Spike.Lib.A64.Rt.rS0_sub (Ly)
  have hfit := Spike.Lib.A64.Rt.fitS_of_sub (Ly) hsub
  have hI := Spike.Lib.A64.PhRec.instOk_ofPlaceOK h i (rS := Spike.Lib.A64.Rt.rS0 (Ly))
  have hZ48 : bareMC.Z.toInt = 48 := by decide
  have hok : (swR (Ret0.stacksA (Ly).lab + 0#64 + 16384#64) (-(D + 48)) 0).OK := by
    rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_hokD _ (by omega) (by omega)
  have h16' : (Ret0.stacksA (Ly).lab + 0#64 + 16384#64).toNat % 16 = 0 := by
    rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_h16 _
  have hmr : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 (Ly).Λ) false
      ⟨limA (UInt64.ofBitVec (Ret0.pinA (Ly).lab + 0#64 + 8#64)), 8⟩ = true := by
    rw [Spike.Lib.A64.Rt.pinA_lab0, Spike.Lib.A64.Rt.limA_tcb0]
    exact ((Ly).words_mapped _ ((Ly).fld_mem (by decide))).2.1
  have hK0 : (ms []).K = some Scc.Sem.A64.abi := by rw [hms]; rfl
  -- the switch's and `scc_rt_main`'s states, the user field at a room no region holds
  have hs3 := swUW_gen_dt (F := FE) (R := entryR E) (D := 2 ^ 65) (Dt := Dt) (p := p) (lbl' := lbl)
    (ms := ms []) (Post := UPostS p lbl Spike.Lib.A64Consumer.c0) (ZU := ZU) (L := D + 48) hI hrc.tail hrc.main
    hC0 (fun c v hv => hv.1 ▸ hC0) hmph hsw h16' hok (by omega) (by omega) (by omega) (by omega) (by decide)
    hmr hsub hfit
    (fun v F'' hR0 => by
      exfalso
      have h1 := hR0.lo
      have h2 := BitVec.isLt (Region.addr (swR v (-(D + 48)) 0) (-bareMC.Z.toInt))
      simp only [Region.callee] at h1
      omega)
  -- `scc_rt_start`'s states up to the switch
  have hA := Spike.Lib.A64.Rt.startAllUW_gen h i (rtPh_of_placeOKAt h) hC0
    (Spike.Lib.A64.Rt.entryR_ok hE) (Spike.Lib.A64.Rt.entryR_al hE) (by show (-65536 : Int) ≤ -304; decide)
    (by show (0 : Int) ≤ 0; decide) hFE rfl (rS0_eq_lab _) hsub
    (stackM_rS0 _ hE).1 (stackM_rS0 _ hE).2.1 (stackM_rS0 _ hE).2.2 hs3
  have H := a64_start_segWS h i hs (p := p) (W := W) hms hfree hE hD0 hD8 hD hGh hGf hGt hownT hG1 hG0 hGn hownL
    hownF hownN hroomM hroomU (uPostS_exit hms) hFE hFEs hFEk hUF hUS (blkW_wmono hmap hEntry)
    ⟨sp0W_wmono hmap hA.s1, sp2W_wmono hmap hA.s2,
      ⟨nodeW_wmono hmap hs3.sw, fun v => blkW_wmono hmap (hs3.blk v), fun v => mainUW_wmono hmap (hs3.main v),
        fun v F' hR hal hF hFF g hra hc htp =>
          segWS_wmono (hU v F' hR hal hF hFF g hra hc htp) fun _ _ _ hw _ => hw⟩⟩ (Q := Q)
  -- the pairs stay `Good1`, so they carry `SFactsS`
  refine (segWS_wmono (H.good1 hp ?_ ?_) fun s c fs hw => hw.1 hw.2).mono_post fun _ _ _ h => h.1
  · rintro s c _ ⟨⟨-, -, -, -, σ, -, -, hJ⟩, rfl⟩
    have hc : c = Spike.Lib.A64Consumer.c0 := hJ
    exact hc ▸ hg0
  · intro s c fs hw hg fs' K' hK' hat buf n hd
    rw [hMs.K fs', hK0] at hK'
    cases hK'
    exact hDt s ((hw hg).wrTail hat 1 buf n hd) hat buf n hd

end StartSG

end Spike.Lib.LowerA64
