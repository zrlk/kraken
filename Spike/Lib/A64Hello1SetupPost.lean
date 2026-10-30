/-
**`hello1.w`'s `scc_rt_main` from the allocator's return at depth**
(AArch64): `hello1_main_post_segW` (`Spike/Lib/A64Hello1Main.lean`) over
segments with frames (`SegWS`, `Spike/Lib/SegS.lean`), `wc_rodata` under
the frame its source call pushed (`setupCall`,
`Spike/Lib/A64Hello1SetupPre.lean`).

`hello1_main_post_segW` runs `wc_rodata`'s rest and `scc_rt_main`'s rest as
one frameless segment, the source's return out of `rodata` a local run
(`hedge`). Here `rodata`'s return pops the frame `fr`: `wc_rodata`'s rest
is a segment at `[fr]` (`SegWS.liftS`), its exit at `.sp0` a pair whose
source is at `ret a` with `fr`'s continuation of invariant `Jr` (`retJ`),
the return taken with the row that lands there (`FrameStep.ret`,
`SegWS.post_run`); `scc_rt_main`'s rest is a segment at `[]`.

- `MainSp0W`, `MainPostW.sp0W`: `scc_rt_main`'s states from `.sp0` inside
  `W` (`MainPostW` without `wc_rodata`'s).
- `hello1_main_sp0_segW`: `scc_rt_main` from `.sp0` (of `wc_rodata`'s
  return invariant `Jr`, left its region) to `print`'s abort, frameless
  (`hello1_main_post_segW`'s second part).
- `retJ`: at `ret a`, the frame `fr`'s continuation of invariant `Jr`.
- `MainPostSW`: `wc_rodata`'s states at `[fr]`, `scc_rt_main`'s at `[]`.
- `hello1_main_post_segWS`: from `wc_rodata`'s `.sp0` at `[fr]` to
  `print`'s abort at `[]`.
-/
import Spike.Lib.A64Hello1SetupPre

namespace Spike.Lib.A64.Flow.Hello1

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (CallerCells LimOk seg_oneW)
open Spike.Lib.A64.Alloc (Call Ea)
open Scc.Cert.Rt.A64 (Lays endOf label_labelGap)

set_option linter.unusedSimpArgs false

/-! ## `scc_rt_main` from `.sp0`, frameless -/

/-- **`scc_rt_main`'s states from `.sp0` inside `W`**, none moved by `K`:
`MainPostW`'s without `wc_rodata`'s. -/
structure MainSp0W (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (ms : MemSide isaLSE2) (σC : AS) (Jr Jw : AS → Ctl → Prop) : Prop where
  sp0 : BlkW W K exe endPc R F (mS0 (_root_.Executable.labels exe).label R σC Jr) mB1
  wc : ∀ g : AS × Ctl, Wc1W W K exe endPc (wR R) (fun m => F m ∧ CallerCells R (-80) (-144) 0 m) ms
    (wJ0 (_root_.Executable.labels exe).label σC Jr g)
  exit : ExitW W K exe endPc R F (mS1 (_root_.Executable.labels exe).label Jw) 40

/-- `MainPostW`'s states from `.sp0`. -/
theorem MainPostW.sp0W {W : Frag isaLSE2} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {F : MachineData → Prop} {ms : MemSide isaLSE2} {m0 : MachineData} {σC : AS}
    {Jp J1 J2 J3 J4 Jr Jw : AS → Ctl → Prop} (h : MainPostW W K exe endPc R F ms m0 σC Jp J1 J2 J3 J4 Jr Jw) :
    MainSp0W W K exe endPc R F ms σC Jr Jw :=
  ⟨h.sp0, h.wc, h.exit⟩

section MainSp0

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`scc_rt_main` from `.sp0` is one segment inside `W`** in any valid
layout of `hello1Prog`, for a caller's state `σC` at `wc_rodata`'s call:
from `.sp0` (`wc_rodata`'s return of invariant `Jr`, left its region), the
`.sp0` block, the call of `wc_main` (`hlimW`, `hsvc`, `hedgeW`) and the
`exit_group` tail (`hok`), as in `hello1_main_post_segW`. The only exit is
`print`'s abort. Its states lie in `W`, none moved by `K` (`hW`). -/
theorem hello1_main_sp0_segW {W : Frag isaLSE2} {K : State → State → Prop}
    (hp : Lays exe SccCode.hello1Prog) (hend : endPc = endOf exe SccCode.hello1Prog)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -288) (hhi : 0 ≤ R.hi)
    (hK : ms.K = some Scc.Sem.A64.abi) {σC : AS} {Jr Jw : AS → Ctl → Prop}
    (hW : MainSp0W W K exe endPc R F ms σC Jr Jw)
    (hlimW : ∀ σx c, Jr σx c → LimOk ms F exe endPc (tcbA σx.regs 8) (σx.regs.SP.toBitVec - (96 : Int64).toBitVec))
    (hsvc : ∀ F' : MachineData → Prop, FStable (pR (wR R)) F' →
      (∀ m, F' m → ((F m ∧ CallerCells R (-80) (-144) 0 m) ∧ CallerCells (wR R) (-96) (-48) 0 m) ∧
        Spike.Lib.A64.Rt.WcRa (wR R) ((_root_.Executable.labels exe).label ".L1_scc_rt_main.sp1") m) →
      ∀ g' : PG, g'.2.2 = ((_root_.Executable.labels exe).label ".L19_wc_main.sp4").toBitVec →
      SegW W K p lbl ms
        (At exe endPc (pR (wR R)) F' (PrintD.N (_root_.Executable.labels exe).label g'.1 g'.2.1 g'.2.2 .svc))
        (At exe endPc (pR (wR R)) F' (PrintD.N (_root_.Executable.labels exe).label g'.1 g'.2.1 g'.2.2 .n5)))
    (hedgeW : ∀ g : AS × Ctl, ∀ σ c, wcJ (wJ0 (_root_.Executable.labels exe).label σC Jr g) σ c →
      ∀ σ' : AS, (∀ k, -96 ≤ k → k < 0 → k % 8 = 0 → σ'.slot k = wcSl σ k) →
      σ'.regs.X0.toBitVec = 0#64 → σ'.regs.X29.toBitVec = σ.slot (-16) → σ'.regs.X30.toBitVec = σ.slot (-8) →
      ∃ c', LocalRun p c c' ∧ Jw σ' c')
    (hok : ∀ s c σx, Jw σx c →
      At exe endPc R F ⟨(_root_.Executable.labels exe).label ".L1_scc_rt_main.sp1" + 4 + 4 + 4, ⟨-80, []⟩,
        fun _ _ => True⟩ s c → SysOk p ms s c (.exitGroup σx.regs.X0.toNat)) :
    SegW W K p lbl ms (At exe endPc R F (mS0 (_root_.Executable.labels exe).label R σC Jr))
      (At exe endPc R F (mAb (_root_.Executable.labels exe).label)) := by
  let lab := (_root_.Executable.labels exe).label
  have hin := hello1_mainIn
  simp only [mainIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨-, hb1⟩, -⟩, hg2⟩ := hin
  have e2 : lab ".L1_scc_rt_main.sp1" = lab ".L1_scc_rt_main.sp0" + Int64.ofNat (4 * 10) :=
    label_labelGap hp hg2
  refine SegW.seq (Q := At exe endPc R F (mWC lab σC Jr))
    (seg_oneW (seg_ndW (by simp [mB1]) mB1_ok hF hR hal (by omega) hhi
      (code_of hp hend hb1 (ofNat4_zero _)) hW.sp0 fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩))
    ((fn_segW (N := mPN lab σC Jr Jw) (E := fun _ : Unit => mAb lab) (fun i => ?_) false).mono_post
      fun _ _ ⟨_, h⟩ => h)
  · simp only [mS0, mWC]; rw [mB1_run]
  · simp only [mS0, mWC]; rw [mB1_run]; rfl
  · simp only [mS0, mWC] at hJ ⊢
    obtain ⟨σx, hJr, rfl⟩ := hJ
    rw [mB1_run]
    refine ⟨σx, hJr, rfl, rfl, rfl, rfl, ?_, rfl, rfl, ?_⟩
    · show (leave (mR R) (-80) σC σx).slot (-80) = _
      simp only [leave]
      exact ite_eq_right (by simp only [Region.Off, Region.callee]; omega)
    · rw [e2]
      show BitVec.ofInt 64 _ = _
      rw [Ret0.ofInt_bmod]
      simp only [BitVec.ofInt_add, Spike.Lib.int64_ofInt_toInt, Int64.toBitVec_add, BitVec.add_assoc]
      rfl
  · cases i
    case false =>
      refine call_nd_FWK (KC := False) (lo' := -144) (hi' := 0) (M := fun _ => True)
        (Ne := fun g : AS × Ctl => ⟨lab "wc_main", ⟨0, []⟩, wJ0 lab σC Jr g⟩)
        (Ex := fun g : AS × Ctl => wX lab (wcJ (wJ0 lab σC Jr g)) (wXr lab Jw))
        hR hal hF (by show R.lo ≤ -80 + -144; omega) (by decide) (by show (-80 : Int) < R.hi; omega) (by decide)
        (by show (-80 : Int) % 16 = 0; decide) (by decide) (by decide) (fun h => h.elim) (fun h => h.elim)
        (fun _ h _ => h)
        (fun R' F' hR' hal' hlo' hhi' hF' _ hFF hR'e hcc g _ _ => by
          subst hR'e
          refine (hello1_wc_segW hp hend hF' hR' hal' hlo' hhi' (x := wXr lab Jw) rfl
            ((hW.wc g).mono fun m h => ⟨hFF m h, hcc m h⟩) ?_ ?_
            (fun F'' hF'' hFF'' g' hg' => hsvc F'' hF''
              (fun m h => ⟨⟨⟨hFF m (hFF'' m h).1.1, hcc m (hFF'' m h).1.1⟩, (hFF'' m h).1.2⟩, (hFF'' m h).2⟩)
              g' hg')
            (hedgeW g)).mono_post fun _ _ ⟨y, h⟩ => ⟨y, h, trivial⟩
          · rintro σ c ⟨rfl, -, σx, hJr, -, -, -, -, -, hsp, htp, -⟩
            have h := (hlimW σx _ hJr).mono (F' := F') hFF
            have ht : tcbA (enter (-80) g.1).regs 8 = tcbA σx.regs 8 := by
              simp only [tcbA, enter, htp]
            rw [ht]
            show LimOk ms _ exe endPc _ (g.1.regs.SP.toBitVec - _)
            rw [hsp]; exact h
          · rintro σ c ⟨rfl, -, σx, -, -, -, -, -, -, -, -, h30⟩
            show lab ".L1_scc_rt_main.sp1" = Int64.ofBitVec g.1.regs.X30.toBitVec
            rw [h30, int64_ofBitVec_toBitVec])
        (fun _ => rfl) ?_ ?_
      · intro σC' c hJ
        exact ⟨(σC', c), rfl, rfl, rfl, hJ⟩
      · rintro _ y σC' c σx c' σR - - hx hreg - -
        cases y
        · exact .inl ⟨true, rfl, rfl, σx, hx, hreg⟩
        · refine .inr ⟨(), rfl, rfl, ?_⟩
          show σR.regs.X0 = 4
          rw [hreg]; exact hx.1
    case true =>
      refine hello1_main_exit_segW hp hend (n := mS1 lab Jw) rfl rfl hK hF hR hal (by omega) hhi hW.exit
        fun s c σ0 ⟨σx, hJ, hr⟩ hAt => ?_
      rw [hr]
      exact hok s c σx hJ hAt

end MainSp0

/-! ## `wc_rodata`'s return pops the source's frame -/

/-- **At a return into the frame `fr`**: the control at `ret a`, `a` of
words `ws`, `fr`'s continuation with `ws` bound of invariant `Jr`. -/
def retJ (fr : TermRun.Frame) (Jr : AS → Ctl → Prop) (σ : AS) (c : Ctl) : Prop :=
  ∃ (a : CoreTerm.At) (t : Ty) (ws : List TermRun.Word), c.term = .ret a ∧ TermRun.evalAt c.env a = some (t, ws) ∧
    Jr σ ⟨fr.body, (fr.x, fr.ty, ws) :: fr.env, none⟩

/-- **`scc_rt_main`'s states from `wc_rodata`'s `.sp0` with frames**:
`wc_rodata`'s under the frame `fr` its source call pushed, `scc_rt_main`'s
from `.sp0` with none. -/
structure MainPostSW (W : FragS isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (ms : List TermRun.Frame → MemSide isaLSE2) (fr : TermRun.Frame)
    (m0 : MachineData) (σC : AS) (Jp J1 J2 J3 J4 Jr Jw : AS → Ctl → Prop) : Prop where
  rd : RdPostW (fun s c => W s c [fr]) K exe endPc (mR R) (mF R F m0 σC) Jp J1 J2 J3 J4
  tl : MainSp0W (fun s c => W s c []) K exe endPc R F (ms []) σC Jr Jw

section MainPostS

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`scc_rt_main` from `wc_rodata`'s `.sp0` at depth**: from `.sp0` in
`wc_rodata`'s region under the frame `fr` (no type variables, `hfr`) to
`print`'s abort with no frame. `wc_rodata`'s rest at `[fr]` under `ms [fr]`
(`hello1_rodata_post_segW` to `scc_rt_main`'s `.sp0` of invariant
`retJ fr Jr`: `hra`, `hmem`, `h1` … `h4`, `hedge` as there), leaving its
region (`at_leave`) and returning into `fr` (`FrameStep.ret`,
`SegWS.post_run`); then `hello1_main_sp0_segW` at `[]` under `ms []`
(`hK`, `hlimW`, `hsvc`, `hedgeW`, `hok`). Its states lie in `W`, none moved
by `K` (`hW`). -/
theorem hello1_main_post_segWS {W : FragS isaLSE2} {K : State → State → Prop} {fr : TermRun.Frame}
    (hp : Lays exe SccCode.hello1Prog) (hend : endPc = endOf exe SccCode.hello1Prog)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -288) (hhi : 0 ≤ R.hi)
    (hK : (ms []).K = some Scc.Sem.A64.abi) (hfr : fr.σs = [])
    {m0 : MachineData} {σC : AS} {Jp J1 J2 J3 J4 Jr Jw : AS → Ctl → Prop}
    (hW : MainPostSW W K exe endPc R F ms fr m0 σC Jp J1 J2 J3 J4 Jr Jw)
    (hra : ∀ σ0 c, Jp σ0 c → (_root_.Executable.labels exe).label ".L1_scc_rt_main.sp0" = Int64.ofBitVec (σ0.slot (-8)))
    (hmem : ∀ σ0 c, Jp σ0 c → ∀ i : Int64, (i = 0 ∨ i = 8) →
      ∀ m, mF R F m0 σC m → Mem.loadInt m.dmem (rAddr σ0.regs .X0 i) 8 = none)
    (h1 : ∀ σ0 c, Jp σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (rAddr σ0.regs .X0 0).toNat ∧ c.hold = none ∧
      ∀ (r : Val) (w' : TermRun.Word), (ms [fr]).rd w' → Scc.Sem.ValRep lbl w'.val (r.setWidth 64).toNat →
        J1 σ0 { c with hold := some ((rAddr σ0.regs .X0 0).toNat, w') })
    (h2 : ∀ σ0 c, J1 σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr) (tv : Ty)
      (wv wold : TermRun.Word),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (rAddr σ0.regs .X0 0).toNat ∧
      c.hold = some ((rAddr σ0.regs .X0 0).toNat, wold) ∧ TermRun.evalAt c.env v = some (tv, [wv]) ∧
      Scc.Sem.ValRep lbl wv.val (rpK1.setWidth 128).toNat ∧ J2 σ0 ⟨e, (x, u, [wold]) :: c.env, none⟩)
    (h3 : ∀ σ0 c, J2 σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (rAddr σ0.regs .X0 8).toNat ∧ c.hold = none ∧
      ∀ (r : Val) (w' : TermRun.Word), (ms [fr]).rd w' → Scc.Sem.ValRep lbl w'.val (r.setWidth 64).toNat →
        J3 σ0 { c with hold := some ((rAddr σ0.regs .X0 8).toNat, w') })
    (h4 : ∀ σ0 c, J3 σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr) (tv : Ty)
      (wv wold : TermRun.Word),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (rAddr σ0.regs .X0 8).toNat ∧
      c.hold = some ((rAddr σ0.regs .X0 8).toNat, wold) ∧ TermRun.evalAt c.env v = some (tv, [wv]) ∧
      Scc.Sem.ValRep lbl wv.val (rpK2.setWidth 128).toNat ∧ J4 σ0 ⟨e, (x, u, [wold]) :: c.env, none⟩)
    (hedge : ∀ σ0 c, J4 σ0 c → ∀ σ' : AS, σ'.regs.X0.toBitVec = σ0.regs.X0.toBitVec →
      σ'.regs.X1.toBitVec = 0#64 → σ'.regs.X2.toBitVec = 2#64 → σ'.regs.X3.toBitVec = 13#64 →
      σ'.regs.X29.toBitVec = σ0.slot (-16) → σ'.regs.X30.toBitVec = σ0.slot (-8) →
      ∃ c', LocalRun p c c' ∧ retJ fr Jr σ' c')
    (hlimW : ∀ σx c, Jr σx c →
      LimOk (ms []) F exe endPc (tcbA σx.regs 8) (σx.regs.SP.toBitVec - (96 : Int64).toBitVec))
    (hsvc : ∀ F' : MachineData → Prop, FStable (pR (wR R)) F' →
      (∀ m, F' m → ((F m ∧ CallerCells R (-80) (-144) 0 m) ∧ CallerCells (wR R) (-96) (-48) 0 m) ∧
        Spike.Lib.A64.Rt.WcRa (wR R) ((_root_.Executable.labels exe).label ".L1_scc_rt_main.sp1") m) →
      ∀ g' : PG, g'.2.2 = ((_root_.Executable.labels exe).label ".L19_wc_main.sp4").toBitVec →
      SegW (fun s c => W s c []) K p lbl (ms [])
        (At exe endPc (pR (wR R)) F' (PrintD.N (_root_.Executable.labels exe).label g'.1 g'.2.1 g'.2.2 .svc))
        (At exe endPc (pR (wR R)) F' (PrintD.N (_root_.Executable.labels exe).label g'.1 g'.2.1 g'.2.2 .n5)))
    (hedgeW : ∀ g : AS × Ctl, ∀ σ c, wcJ (wJ0 (_root_.Executable.labels exe).label σC Jr g) σ c →
      ∀ σ' : AS, (∀ k, -96 ≤ k → k < 0 → k % 8 = 0 → σ'.slot k = wcSl σ k) →
      σ'.regs.X0.toBitVec = 0#64 → σ'.regs.X29.toBitVec = σ.slot (-16) → σ'.regs.X30.toBitVec = σ.slot (-8) →
      ∃ c', LocalRun p c c' ∧ Jw σ' c')
    (hok : ∀ s c σx, Jw σx c →
      At exe endPc R F ⟨(_root_.Executable.labels exe).label ".L1_scc_rt_main.sp1" + 4 + 4 + 4, ⟨-80, []⟩,
        fun _ _ => True⟩ s c → SysOk p (ms []) s c (.exitGroup σx.regs.X0.toNat)) :
    SegWS W K p lbl ms
      ((At exe endPc (mR R) (mF R F m0 σC) (pN (_root_.Executable.labels exe).label Jp J1 J2 J3 J4 .s0)).at [fr])
      ((At exe endPc R F (mAb (_root_.Executable.labels exe).label)).at []) := by
  let lab := (_root_.Executable.labels exe).label
  obtain ⟨hR', hal', hF'⟩ := mR_ok hR hal hF hlo hhi m0 σC
  refine SegWS.seq (Q := (At exe endPc R F (mS0 lab R σC Jr)).at []) (SegWS.post_run ?_)
    (SegWS.liftS [] (hello1_main_sp0_segW hp hend hF hR hal hlo hhi hK hW.tl hlimW hsvc hedgeW hok)
      fun _ _ h => h)
  refine (SegWS.liftS [fr] (hello1_rodata_post_segW hp hend hF' hR' hal' (by show (-208 : Int) ≤ -48; decide)
    (by show (0 : Int) ≤ 0; decide) (x := ⟨lab ".L1_scc_rt_main.sp0", ⟨0, []⟩, retJ fr Jr⟩) rfl hW.rd hra hmem
    h1 h2 h3 h4 hedge) fun _ _ h => h).mono_post ?_
  rintro s c fs ⟨h, rfl⟩
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, σx, σC', ⟨a, t, ws, hc, ha, hJ⟩, rfl, hσ⟩ :=
    at_leave (P := fun σ => σ = σC) rfl (fun m hm => ⟨hm.1, m0, σC, ⟨-80, []⟩, hm.2.1, hm.2.2, rfl⟩) h
  exact ⟨_, [], .single (FrameStep.ret hc hfr ha), ⟨he, hn, hdc, hpc, σ, hA, hD, σx, hJ, hσ⟩, rfl⟩

end MainPostS

end Spike.Lib.A64.Flow.Hello1
