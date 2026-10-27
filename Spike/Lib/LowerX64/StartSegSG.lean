/-
**The loaded thread's run at depth inside `SFactsS`** (x86-64, H7a calls):
`x64_start_segWS` (`Spike/Lib/LowerX64/StartSegS.lean`) with the runtime's
obligations from the call-free ones inside `SFacts … Dt` (`st0W_gen`,
`x0W_of_bare`, `swUW_gen_dt`, `_start`'s `EntryW`), the user function's
interface `UserCallWS` inside `SFactsS … Dt` (e.g. `userCallWS_of_exitCL`,
`Spike/Lib/LowerX64/UserLag.lean`), `main`'s exit at the post `UPostS`.

The runtime's obligations hold at every control, but `SFactsS` at a pair
holds only for a `Good1` one (`SFactsS.ofSFacts0`): they are lifted to the
world `Good1 p (c, fs) → SFactsS …` (the `*_wmono` lemmas), where the user
function's interface lies too, and the segment from the entry (whose pair
is `Good1`, `hg0`) keeps its pairs `Good1` (`SegWS.good1`,
`Spike/Lib/SegGood1.lean`), so they carry `SFactsS`.

- `st0W_wmono`, `x0W_wmono`, `mainUW_wmono`: `scc_rt_start`'s and
  `scc_rt_main`'s obligations in a larger `W`.
- `x64_start_segWSG`: the run from `_start` one segment at depth inside
  `SFactsS … Dt`, at any callee room `D` of the user `main`.
-/
import Spike.Lib.LowerX64.StartSegS
import Spike.Lib.LowerX64.StartU
import Spike.Lib.LowerX64.UPostS
import Spike.Lib.LowerX64.UserLag
import Spike.Lib.Rt.X64RtStartU
import Spike.Lib.SegGood1

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib.X64Consumer (CFacts SFacts Lbl Lsize msOf)
open Spike.Lib.X64ConsumerS (SFactsS)
open Spike.Lib.X64.Rt (RuntimeLayout StartAllUWS SwUWS EntryW nilW bareMC rtF entryR entryN0 MainUW)
open Spike.Lib.X64.Rt.StartU (blkW_wmono nodeW_wmono tcbW_wmono tiW_wmono)
open Spike.Lib.X64.Flow.Ret0 (StackM limA tpOf St0W X0W)
open Spike.Lib.X64.PhRec (μ K)

section WMono

variable {W W' : Frag isa} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64} {R : Region}
  {F : MachineData → Prop}

/-- `scc_rt_start`'s obligations up to `.x0` in a larger `W`. -/
theorem st0W_wmono (hW : ∀ s c, W s c → W' s c) {n0 : BitVec 64} {c0 : Ctl}
    (h : St0W W K exe endPc R F n0 c0) : St0W W' K exe endPc R F n0 c0 :=
  ⟨⟨blkW_wmono hW h.start.w0, nodeW_wmono hW h.start.w1, blkW_wmono hW h.start.w2, nodeW_wmono hW h.start.w3⟩,
    blkW_wmono hW h.blk, fun g hg i => tcbW_wmono hW (h.tcb g hg i)⟩

/-- `scc_rt_start`'s obligations from `.x0` to the switch in a larger `W`. -/
theorem x0W_wmono (hW : ∀ s c, W s c → W' s c) {rS : Scc.Sem.Range} {n0 k0 : BitVec 64} {c0 : Ctl}
    (h : X0W W K exe endPc R F rS n0 k0 c0) : X0W W' K exe endPc R F rS n0 k0 c0 :=
  ⟨blkW_wmono hW h.b0, fun g hg i => tiW_wmono hW (h.ti g hg i), blkW_wmono hW h.fs, nodeW_wmono hW h.sys,
    blkW_wmono hW h.sw⟩

/-- `scc_rt_main`'s own obligations in a larger `W`. -/
theorem mainUW_wmono (hW : ∀ s c, W s c → W' s c) {ms : MemSide isa} {mc : Spike.Lib.X64.Rt.MainCode}
    {Post : Ctl → BitVec 64 → Prop} {g : Ret0.MainG} (h : MainUW W K exe endPc R F ms mc Post g) :
    MainUW W' K exe endPc R F ms mc Post g :=
  ⟨⟨blkW_wmono hW h.pro.w0, blkW_wmono hW h.pro.w1, nodeW_wmono hW h.pro.w2, blkW_wmono hW h.pro.w3,
      blkW_wmono hW h.pro.w4⟩,
    blkW_wmono hW h.call, ⟨blkW_wmono hW h.exit.w0, nodeW_wmono hW h.exit.w1⟩⟩

end WMono

section StartSG

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
  (h : placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option quotPrecheck false

/-- The runtime's layout of the output. -/
local notation "Ly" => RuntimeLayout.ofPlaceOK h i

/-- **The call-free facts of the start's run**: `SFacts` at the record, the
first stack `rS0` taken, the write tail `Dt`. -/
local notation "WS" lbl:max Dt:max => fun s c => SFacts (Ly).Λ (μ (Ly)) (Spike.Lib.X64.PhRec.own (Ly))
  (Spike.Lib.X64.Rt.rS0 (Ly)) (Spike.Lib.X64.PhRec.Tk (Ly)) lbl s c Dt

/-- **The facts at depth of the start's run**: `SFactsS` at the record, the
owned words not depending on the frames. -/
local notation "WSS" p:max lbl:max cl:max ctr:max Dt:max => fun s c fs => SFactsS (Ly).Λ (μ (Ly)) p
  (fun s _ => Spike.Lib.X64.PhRec.own (Ly) s) (Spike.Lib.X64.Rt.rS0 (Ly)) (Spike.Lib.X64.PhRec.Tk (Ly)) lbl cl ctr
  s c fs Dt

/-- The placement's memory side at the record. -/
local notation "MS" rd:max G:max lbl:max lsize:max =>
  msOf (Ly).Λ (μ (Ly)) rd G (Spike.Lib.X64.PhRec.own (Ly)) lbl lsize

/-- The callee region of `_start`'s call at the entry state `E`, where
`scc_rt_start` runs. -/
local notation "EC" E:max => (entryR E).callee (-8) (-296) 8

/-- **The loaded thread's run is one segment at depth inside `SFactsS …
Dt`**, for an `Accepted1` program `p` (`hp`) whose start control is `Good1`
(`hg0`), under memory sides with frames agreeing with the placement's with
no frame (`hms`, `hMs`), a write tail `Dt` whose system calls are no `write` to the output
(`hDt`): `x64_start_segWS`'s premises at the post `UPostS` (`main`'s exit
by `uPostS_exit`) but `hEntry` and `hW`, which come from `_start`'s
obligations inside `SFacts … Dt` (`hEntry`), `st0W_gen`, `x0W_of_bare` and
`swUW_gen_dt`'s (its user field at a room no region holds) at `c0`'s facts
(`hC0`) and `scc_rt_main`'s phase facts (`hmph`, `hsw`), and the user
function's interface inside `SFactsS … Dt` (`hU`), from the entry frame
condition `FE` (implying `rtF`, stable, kept by the take), whose private
memory's facts `U` (kept in the new stack's region) the interface's frame
conditions carry. -/
theorem x64_start_segWSG (hs : o.place.tail = .bare) {p : Prog} (hp : Scc.Lower.Accepted1 p = true)
    (hg0 : Good1 p (Spike.Lib.X64Consumer.c0, []))
    {ms : List TermRun.Frame → MemSide isa} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {lbl : Lbl}
    {lsize : Lsize} (hms : ms [] = MS rd G lbl lsize) (hMs : MsAgree ms) {Dt : State → Prop}
    (hDt : ∀ s, Dt s → Scc.Sem.X64.abi.atSys s = true → ∀ buf n,
      Scc.Sem.Kernel.decode Scc.Sem.X64.abi.nrs (Scc.Sem.X64.abi.nr s) (Scc.Sem.X64.abi.arg s) ≠
        some (.write 1 buf n))
    {cl ctr : Nat}
    (hfree : Spike.Lib.X64.Rt.RtFree (Ly) lbl lsize)
    {E : Scc.Sem.Entry} (hE : E.Ok (Ly).Λ)
    {D : Int} (hD0 : 0 ≤ D) (hD8 : D % 8 = 0) (hD : D + 56 ≤ 16384) {ZU : Int64}
    (hGh : G ⟨(Ly).pinA + 0#64, 8⟩ ((Ret0.AllocTcb.hdr0 ||| 1#64 <<< 36).setWidth 128))
    (hGf : ∀ e ∈ Ret0.ThreadInit.fields ((Ly).pinA + 0#64 + 8#64) ((Ly).stacksA + 0#64),
      G ⟨(Ly).pinA + 0#64 + 8#64 + BitVec.ofNat 64 e.1, 8⟩ (e.2.setWidth 128))
    (hGt : G ⟨(Ly).pnA, 8⟩ ((0#64 + Ret0.AllocTcb.tcbLen).setWidth 128))
    (hownT : OwnAt (MS rd G lbl lsize) (Ly).exe (Ly).endPc (Ret0.AllocTcb.rmwPc (Ly).lab) (Ly).pnA 0#64)
    (hG1 : G ⟨(Ly).lockA, 8⟩ ((1#64).setWidth 128)) (hG0 : G ⟨(Ly).lockA, 8⟩ ((0#64).setWidth 128))
    (hGn : G ⟨(Ly).nextA, 8⟩ ((0#64 + Ret0.StackTake.size0).setWidth 128))
    (hownL : OwnAt (MS rd G lbl lsize) (Ly).exe (Ly).endPc (Ret0.StackTake.swpPc (Ly).lab) (Ly).lockA 0#64)
    (hownF : OwnAt (MS rd G lbl lsize) (Ly).exe (Ly).endPc (Ret0.StackTake.freeNPc (Ly).lab) (Ly).freeNA 0#64)
    (hownN : OwnAt (MS rd G lbl lsize) (Ly).exe (Ly).endPc (Ret0.StackTake.nextPc (Ly).lab) (Ly).nextA 0#64)
    (hroomM : ∀ v : Val, G ⟨limA (tpOf ((Ly).pinA + 0#64 + 8#64)), 8⟩ v →
      (v.setWidth 64).toNat ≤ (Ret0.stacksA (Ly).lab + 0#64 + 16384#64 - 8#64 - 8#64 - bareMC.Z.toBitVec).toNat)
    (hroomU : ∀ v : Val, G ⟨limA (tpOf ((Ly).pinA + 0#64 + 8#64)), 8⟩ v →
      (v.setWidth 64).toNat ≤ (Ret0.stacksA (Ly).lab + 0#64 + 16384#64 - 8#64 - 8#64 - bareMC.Z.toBitVec -
        8#64 - 8#64 - ZU.toBitVec).toNat)
    (hC0 : CFacts (Ly).Λ lbl Spike.Lib.X64Consumer.c0)
    (hmph : Spike.Lib.X64.Rt.MainU.MainPh (Spike.Lib.X64.PhRec.okPc (Ly)) (Spike.Lib.X64.PhRec.ph (Ly)) (Ly).lab
      bareMC)
    (hsw : Spike.Lib.X64.Rt.MainU.SwPh (Spike.Lib.X64.PhRec.okPc (Ly)) (Spike.Lib.X64.PhRec.ph (Ly)) (Ly).lab)
    {FE : MachineData → Prop} (hFE : ∀ m, FE m → rtF (Ly) m) (hFEs : FStable (entryR E) FE)
    (hFEk : ∀ m pm, FE m → FE (Ret0.takeMem pm (Spike.Lib.X64.Rt.rS0 (Ly)) m))
    {U : _root_.Mem 64 → Prop} (hUF : ∀ m, FE m → U m.dmem)
    (hUS : FStable (swR (Ret0.stacksA (Ly).lab + 0#64 + 16384#64) (-(D + 56)) 0) fun m => U m.dmem)
    (hEntry : EntryW (WS lbl Dt) (K (Ly) (Spike.Lib.X64.Rt.rS0 (Ly))) (Ly).exe (Ly).endPc (entryR E) FE
      (Ly).lab Spike.Lib.X64Consumer.c0)
    (hU : ∀ v (F' : MachineData → Prop),
      (∀ m, F' m → (Spike.Lib.X64.Rt.swFSL (D + 56) (Spike.Lib.X64.Rt.rS0 (Ly))
          (Ret0.stacksA (Ly).lab + 0#64 + 16384#64) (limA (tpOf (Ret0.pinA (Ly).lab + 0#64 + 8#64))) v m ∧
        Ret0.CallerCells (swR v (-(D + 56)) 0) (-8 - 0) (8 - (D + 56)) 8 m) ∧ U m.dmem) →
      Spike.Lib.X64.Rt.UserCallWS (WSS p lbl cl ctr Dt) (K (Ly) (Spike.Lib.X64.Rt.rS0 (Ly))) p lbl ms (Ly).exe
        (Ly).endPc ((swR v (-(D + 56)) 0).callee (-8 - 0) (8 - (D + 56)) 8) F' bareMC.fn bareMC.Z D ZU
        (UPostS p lbl Spike.Lib.X64Consumer.c0) ((_root_.Executable.labels (Ly).exe).label bareMC.sp0).toBitVec
        Spike.Lib.X64Consumer.c0 (tpOf (Ret0.pinA (_root_.Executable.labels (Ly).exe).label + 0#64 + 8#64)))
    {Q : FragS isa} :
    SegWS (WSS p lbl cl ctr Dt) (K (Ly) (Spike.Lib.X64.Rt.rS0 (Ly))) p lbl ms
      ((At (Ly).exe (Ly).endPc (entryR E) FE (entryN0 (Ly).lab Spike.Lib.X64Consumer.c0)).at []) Q := by
  -- the world of the lift: `SFactsS` at the `Good1` pairs
  let W : FragS isa := fun s c fs => Good1 p (c, fs) → SFactsS (Ly).Λ (μ (Ly)) p
    (fun s _ => Spike.Lib.X64.PhRec.own (Ly) s) (Spike.Lib.X64.Rt.rS0 (Ly)) (Spike.Lib.X64.PhRec.Tk (Ly)) lbl cl ctr
    s c fs Dt
  have hmap : ∀ s c, (WS lbl Dt) s c → nilW W s c := fun s c hw hg => SFactsS.ofSFacts0 hw hp hg
  have hrc := Spike.Lib.X64.Rt.rtCodeIn_of_ok (rtCodeOk_bare_of_placeOKAt h hs)
  have hsub := Spike.Lib.X64.Rt.rS0_sub (Ly)
  have hfit := Spike.Lib.X64.Rt.fitS_of_sub (Ly) hsub
  have hI := Spike.Lib.X64.PhRec.instOk_ofPlaceOK h i (rS := Spike.Lib.X64.Rt.rS0 (Ly))
  obtain ⟨hZ, hZ8, hps, hkm⟩ := Spike.Lib.X64.Rt.bareMC_ok
  have hZ32 : bareMC.Z.toInt = 32 := by decide
  have hok : (swR (Ret0.stacksA (Ly).lab + 0#64 + 16384#64) (-(D + 56)) 0).OK := by
    rw [Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rt_hokD _ (by omega) (by omega)
  have h8 : (Ret0.stacksA (Ly).lab + 0#64 + 16384#64).toNat % 8 = 0 := by
    rw [Spike.Lib.X64.Rt.stacksA_lab0]; have := Spike.Lib.X64.Rt.rt_h16 (Ly); omega
  have hmr : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 (Ly).Λ) false
      ⟨limA (tpOf (Ret0.pinA (Ly).lab + 0#64 + 8#64)), 8⟩ = true := by
    rw [Spike.Lib.X64.Rt.pinA_lab0, Spike.Lib.X64.Rt.limA_tcb0]
    exact ((Ly).words_mapped _ ((Ly).fld_mem (by decide))).2.1
  have hrS : Spike.Lib.X64.Rt.rS0 (Ly) = ⟨(Ret0.stacksA (Ly).lab + 0#64).toNat, 16384⟩ := by
    rw [Spike.Lib.X64.Rt.rS0, ← (Ly).lab_stacks]
  have hK0 : (ms []).K = some Scc.Sem.X64.abi := by rw [hms]; rfl
  have H := x64_start_segWS h i hs (p := p) (W := W) hms hfree hE hD0 hD8 hD hGh hGf hGt hownT hG1 hG0 hGn hownL
    hownF hownN hroomM hroomU (uPostS_exit hms) hFE hFEs hFEk hUF hUS (hEntry.mono hmap) (Q := Q)
    fun F' hF' hK' hFF => by
      have hEC := ec_facts _ hE hsub
      -- the switch's and `scc_rt_main`'s states, the user field at a room no region holds
      have hs3 := swUW_gen_dt (F := F') (R := EC E) (D := 2 ^ 65) (Dt := Dt) (p := p) (lbl' := lbl) (ms := ms [])
        (Post := UPostS p lbl Spike.Lib.X64Consumer.c0) (ZU := ZU) hI hrc.tail hrc.main hC0
        (fun c v hv => hv.1 ▸ hC0) hmph hsw h8 hok (by omega) (by omega) hZ hZ8 hps hkm hmr hsub hfit
        (fun v F'' _ F''' hR0 => by
          exfalso
          have h1 := hR0.lo
          have h2 := BitVec.isLt (Region.addr ((swR v (-(D + 56)) 0).callee (-8 - 0) (8 - (D + 56)) 8)
            (-8 - bareMC.Z.toInt - 8 - 0))
          simp only [Region.callee] at h1
          omega)
      refine ⟨st0W_wmono hmap (Spike.Lib.X64.Rt.st0W_gen h i hC0 hEC.1 hEC.2.1 hEC.2.2.1 hFF),
        x0W_wmono hmap (Spike.Lib.X64.Rt.x0W_of_bare h i hs hC0 hEC.1 hEC.2.1 hEC.2.2.1 hFF hrS hsub hEC.2.2.2.2),
        ⟨nodeW_wmono hmap hs3.sw, fun v => nodeW_wmono hmap (hs3.xor v), fun v => blkW_wmono hmap (hs3.blk v),
          fun v => mainUW_wmono hmap (hs3.main v),
          fun v F'' hF'' => fun F''' hR0 hF''' hFF'' g hra hc htp =>
            (hU v F'' hF'' F''' hR0 hF''' hFF'' g hra hc htp).mono_W fun _ _ _ hw _ => hw⟩⟩
  -- the pairs stay `Good1`, so they carry `SFactsS`
  refine ((H.good1 hp ?_ ?_).mono_W fun s c fs hw => hw.1 hw.2).mono_post fun _ _ _ h => h.1
  · rintro s c _ ⟨⟨-, -, -, -, σ, -, -, hJ⟩, rfl⟩
    have hc : c = Spike.Lib.X64Consumer.c0 := hJ
    exact hc ▸ hg0
  · intro s c fs hw hg fs' K' hK' hat buf n hd
    rw [hMs.K fs', hK0] at hK'
    cases hK'
    exact hDt s ((hw hg).wrTail hat 1 buf n hd) hat buf n hd

end StartSG

end Spike.Lib.LowerX64
