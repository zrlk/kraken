/-
**`hello1.w`'s `scc_rt_main` from the allocator's return at depth**
(x86-64): `hello1_main_post_segW` (`Spike/Lib/X64Hello1Main.lean`) over
segments with frames (`SegWS`, `Spike/Lib/SegS.lean`), `wc_rodata` under
the frame its source call pushed (`setupCall`,
`Spike/Lib/X64Hello1SetupPre.lean`). The x86-64 twin of
`Spike/Lib/A64Hello1SetupPost.lean`.

`hello1_main_post_segW` runs `wc_rodata`'s rest and `scc_rt_main`'s rest as
one frameless segment, the source's return out of `rodata` a local run
(`hedge`). Here `rodata`'s return pops the frame `fr`: `wc_rodata`'s rest
is a segment at `[fr]` (`SegWS.liftS`), its exit at `.x2` a pair whose
source is at `ret a` with `fr`'s continuation of invariant `Jr` (`retJ`),
the return taken with the row that lands there (`FrameStep.ret`,
`SegWS.post_run`); `scc_rt_main`'s rest is a segment at `[]`.

- `MainX2W`, `MainPostW.x2W`: `scc_rt_main`'s states from `.x2` inside
  `W` (`MainPostW` without `wc_rodata`'s).
- `hello1_main_x2_segW`: `scc_rt_main` from `.x2` (of `wc_rodata`'s
  return invariant `Jr`, left its region) to `print`'s abort, frameless
  (`hello1_main_post_segW`'s second part).
- `retJ`: at `ret a`, the frame `fr`'s continuation of invariant `Jr`.
- `MainPostSW`: `wc_rodata`'s states at `[fr]`, `scc_rt_main`'s at `[]`.
- `hello1_main_post_segWS`: from `wc_rodata`'s `.x13` at `[fr]` to
  `print`'s abort at `[]`.

Where x86-64 differs from AArch64: `scc_rt_main`'s block after the return is
`.x2` (AArch64's `.sp0`, hence `MainX2W`, `hello1_main_x2_segW`), and
`wc_rodata`'s rest starts at `.x13` (`rdX13`); `%rbp`'s offset at the two
returns is a premise (`hbpr`, `hbpw`, as in `hello1_main_post_segW`), the
return's `At` carrying it (`At.rbp_addr`); `8 ≤ R.hi`, no alignment.
-/
import Spike.Lib.X64Hello1SetupPre

namespace Spike.Lib.X64.Flow.Hello1

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Ret0 (CallerCells LimOk seg_oneW)
open Spike.Lib.X64.Alloc (Call Ea)
open Scc.Cert.Rt.X64 (Lays endOf code_field label_labelGapB)

set_option linter.unusedSimpArgs false

/-! ## `scc_rt_main` from `.x2`, frameless -/

/-- **`scc_rt_main`'s states from `.x2` inside `W`**, none moved by `K`:
`MainPostW`'s without `wc_rodata`'s. -/
structure MainX2W (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (ms : MemSide isa) (σC : AS) (Jr Jw : AS → Ctl → Prop) : Prop where
  x2 : BlkW W K exe endPc R F (mS0 (_root_.Executable.labels exe).label R σC Jr) mB1
  wc : ∀ g : AS × Ctl, Wc1W W K exe endPc (wR R) (fun m => F m ∧ CallerCells R (-80) (-144) 8 m) ms
    (wJ0 (_root_.Executable.labels exe).label σC Jr g)
  exit : XExitW W K exe endPc R F (mS1R (_root_.Executable.labels exe).label Jw) (-72) (-8) (-48) 4 4 5

/-- `MainPostW`'s states from `.x2`. -/
theorem MainPostW.x2W {W : Frag isa} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {F : MachineData → Prop} {ms : MemSide isa} {m0 : MachineData} {σC : AS}
    {Jp J1 J2 J3 J4 Jr Jw : AS → Ctl → Prop} (h : MainPostW W K exe endPc R F ms m0 σC Jp J1 J2 J3 J4 Jr Jw) :
    MainX2W W K exe endPc R F ms σC Jr Jw :=
  ⟨h.x2, h.wc, h.exit⟩

section MainX2

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`scc_rt_main` from `.x2` is one segment inside `W`** in any valid
layout of `hello1Cells`, for a caller's state `σC` at `wc_rodata`'s call:
from `.x2` (`wc_rodata`'s return of invariant `Jr`, left its region, `%rbp`
at the saved `%rbp`, `hbpr`), the `.x2` block, the call of `wc_main`
(`hlimW`, `hsvc`, `hedgeW`) and the `exit_group` tail (`hbpw`, `hok`), as in
`hello1_main_post_segW`. The only exit is `print`'s abort. Its states lie in `W`, none moved by `K` (`hW`). -/
theorem hello1_main_x2_segW {W : Frag isa} {K : State → State → Prop}
    (hp : Lays exe SccCode.hello1Cells) (hend : endPc = endOf exe SccCode.hello1Cells)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -288) (hhi : 8 ≤ R.hi)
    (hK : ms.K = some Scc.Sem.X64.abi) {σC : AS} {Jr Jw : AS → Ctl → Prop}
    (hW : MainX2W W K exe endPc R F ms σC Jr Jw)
    (hbpr : ∀ σx c, Jr σx c → σx.regs.get64 .rbp = R.addr (-8))
    (hlimW : ∀ σx c, Jr σx c → LimOk ms F (σx.regs.fsBase.toBitVec + (8 : Int64).toBitVec)
      (σx.regs.rsp.toBitVec - 8#64 - 8#64 - (80 : Int64).toBitVec))
    (hsvc : ∀ F' : MachineData → Prop, FStable (pR (wR R)) F' →
      (∀ m, F' m → ((F m ∧ CallerCells R (-80) (-144) 8 m) ∧ CallerCells (wR R) (-96 - 8) (-40) 16 m) ∧
        Spike.Lib.X64.Rt.WcRa (wR R) ((_root_.Executable.labels exe).label ".Lscc_rt_main.x3") m ∧
        Spike.Lib.X64.Rt.WcFp (wR R) (R.addr (-8)) m) →
      ∀ g' : PG, g'.2.2 = ((_root_.Executable.labels exe).label ".Lwc_main.x15").toBitVec →
      g'.2.1 = (wR R).addr (-8) →
      SegW W K p lbl ms
        (At exe endPc (pR (wR R)) F' (Print.N (_root_.Executable.labels exe).label g'.1 g'.2.1 g'.2.2 .sys))
        (At exe endPc (pR (wR R)) F' (Print.N (_root_.Executable.labels exe).label g'.1 g'.2.1 g'.2.2 .n5)))
    (hedgeW : ∀ g : AS × Ctl, ∀ σ c, wcJ (wJ0 (_root_.Executable.labels exe).label σC Jr g) σ c →
      σ.regs.get64 .rbp = (wR R).addr (-8) → ∀ σ' : AS,
      (∀ k, -88 ≤ k → k < 8 → k % 8 = 0 → σ'.slot k = wcSl (_root_.Executable.labels exe).label σ k) →
      σ'.regs.rax.toBitVec = 0#64 → σ'.regs.rbp.toBitVec = σ.slot (-8) →
      σ'.regs.rsp.toBitVec = σ.regs.rbp.toBitVec + 8#64 + 8#64 →
      ∃ c', LocalRun p c c' ∧ Jw σ' c')
    (hbpw : ∀ σx c, Jw σx c → σx.regs.get64 .rbp = R.addr (-8))
    (hok : ∀ s c σx, Jw σx c →
      At exe endPc R F ⟨(_root_.Executable.labels exe).label ".Lscc_rt_main.x3" + Int64.ofNat 4 + Int64.ofNat 4 +
        Int64.ofNat 5, mO, fun _ _ => True⟩ s c → SysOk p ms s c (.exitGroup σx.regs.rax.toNat)) :
    SegW W K p lbl ms (At exe endPc R F (mS0 (_root_.Executable.labels exe).label R σC Jr))
      (At exe endPc R F (mAb (_root_.Executable.labels exe).label)) := by
  let lab := (_root_.Executable.labels exe).label
  have hin := hello1_mainIn
  simp only [mainIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨-, hb1⟩, -⟩, hg2⟩ := hin
  have e41 : lab ".Lscc_rt_main.x3" = lab ".Lscc_rt_main.x2" + Int64.ofNat 41 := label_labelGapB hp hg2
  refine SegW.seq (Q := At exe endPc R F (mWC lab σC Jr))
    (seg_oneW (seg_ndW (by simp [mB1]) mB1_ok hF hR hlo hhi
      (code_field hp hend hb1 (ofNat_zero' _)) hW.x2 fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩))
    ((fn_segW (N := mPN lab σC Jr Jw) (E := fun _ : Unit => mAb lab) (fun i => ?_) false).mono_post
      fun _ _ ⟨_, h⟩ => h)
  · simp only [mS0, mWC]; rw [mB1_run]
  · simp only [mS0, mWC]; rw [mB1_run]; rfl
  · simp only [mS0, mWC] at hJ ⊢
    obtain ⟨σx, hJr, rfl⟩ := hJ
    rw [mB1_run]
    refine ⟨σx, hJr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Reg64s.set64, leave]
    · simp [Reg64s.set64, leave]
    · simp [Reg64s.set64, leave]
    · simp [Reg64s.set64, leave]
    · simp only [Reg64s.set64]
      show (leave (mR R) (-80) σC σx).slot (-16) = _
      simp only [leave]
      exact ite_eq_right (by simp only [Region.Off, Region.callee]; omega)
    · simp [Reg64s.set64, leave]
    · simp [Reg64s.set64, leave]
    · simp [Reg64s.set64, leave]
    · rw [e41]
      simp only [upd_apply, ↓reduceIte, Int64.toBitVec_add]
      rfl
  · cases i
    case false =>
      refine call_nd_FWK (KC := False) (e0 := 0) (lo' := -144) (hi' := 8) (M := fun _ => True)
        (Ne := fun g : AS × Ctl => ⟨lab "wc_main", ⟨0, []⟩, wJ0 lab σC Jr g⟩)
        (Ex := fun g : AS × Ctl => wX lab (wcJ (wJ0 lab σC Jr g)) (wXr lab Jw))
        hR hF (by show R.lo ≤ -80 - 0 + -144; omega) (by decide) (by show (-80 : Int) - 0 < R.hi; omega)
        (by show (-80 : Int) - 0 + 8 ≤ R.hi; omega) (by show ((-80 : Int) - 0) % 8 = 0; decide) (by decide)
        (by decide) (fun h => h.elim) (fun h => h.elim) (fun _ h _ => h)
        (fun R' F' hR' hlo' hhi' hF' _ hFF hR'e hcc g _ _ => by
          subst hR'e
          refine (hello1_wc_segW hp hend hF' hR' hlo' hhi' (x := wXr lab Jw) rfl
            ((hW.wc g).mono fun m h => ⟨hFF m h, hcc m h⟩) ?_ ?_ (fp := R.addr (-8)) ?_
            (fun F'' hF'' hFF'' g' hg' hg1 => hsvc F'' hF''
              (fun m h => ⟨⟨⟨hFF m (hFF'' m h).1.1, hcc m (hFF'' m h).1.1⟩, (hFF'' m h).1.2⟩, (hFF'' m h).2⟩)
              g' hg' hg1)
            (hedgeW g)).mono_post fun _ _ ⟨y, h⟩ => ⟨y, h, trivial⟩
          · rintro σ c ⟨rfl, -, σx, hJr, -, -, -, -, -, hsp, hfs, -, -⟩
            have h := (hlimW σx _ hJr).mono (F' := F') hFF
            show LimOk ms F' (g.1.regs.fsBase.toBitVec + _) (g.1.regs.rsp.toBitVec - _ - _)
            rw [hfs, hsp]; exact h
          · rintro σ c ⟨rfl, -, σx, -, -, -, -, -, -, -, -, -, h80⟩
            show lab ".Lscc_rt_main.x3" = Int64.ofBitVec (g.1.slot (-80 + 0))
            rw [show (-80 : Int) + 0 = -80 by decide, h80, int64_ofBitVec_toBitVec]
          · rintro σ c ⟨rfl, -, σx, hJr, -, -, -, -, -, -, -, hbp, -⟩
            show g.1.regs.get64 .rbp = _
            simp only [Reg64s.get64] at hbpr ⊢
            rw [hbp]; exact hbpr σx _ hJr)
        (fun _ => rfl) ?_ ?_
      · intro σC' c hJ
        exact ⟨(σC', c), rfl, rfl, rfl, hJ⟩
      · rintro _ y σC' c σx c' σR - - hx hreg - - -
        cases y
        · exact .inl ⟨true, rfl, by show SO.le ⟨-72, []⟩ ⟨-80 - 0 + 8, []⟩ = true; decide, σx, hx, hreg⟩
        · refine .inr ⟨(), rfl, by show SO.le ⟨-224, []⟩ ⟨-80 - 0 + -144, []⟩ = true; decide, ?_⟩
          show σR.regs.get64 .rdi = 4
          rw [hreg]; exact hx.1
    case true =>
      refine (hello1_main_exit_segW hp hend (n := mS1R lab Jw) rfl rfl hK hF hR (by omega) (by omega) hW.exit
        fun s c σ0 hJ0 hAt => ?_).mono_pre
        fun _ _ h => At.rbp_addr h fun σ c hJ0 => by
          obtain ⟨σx, hJ, hr⟩ := hJ0
          show σ.regs.get64 .rbp = _
          simp only [Reg64s.get64, hr]
          exact hbpw σx c hJ
      obtain ⟨σx, hJ, hr⟩ := hJ0
      rw [hr]
      exact hok s c σx hJ hAt

end MainX2

/-! ## `wc_rodata`'s return pops the source's frame -/

/-- **At a return into the frame `fr`**: the control at `ret a`, `a` of
words `ws`, `fr`'s continuation with `ws` bound of invariant `Jr`. -/
def retJ (fr : TermRun.Frame) (Jr : AS → Ctl → Prop) (σ : AS) (c : Ctl) : Prop :=
  ∃ (a : CoreTerm.At) (t : Ty) (ws : List TermRun.Word), c.term = .ret a ∧ TermRun.evalAt c.env a = some (t, ws) ∧
    Jr σ ⟨fr.body, (fr.x, fr.ty, ws) :: fr.env, none⟩

/-- **`scc_rt_main`'s states from `wc_rodata`'s `.x13` with frames**:
`wc_rodata`'s under the frame `fr` its source call pushed, `scc_rt_main`'s
from `.x2` with none. -/
structure MainPostSW (W : FragS isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (ms : List TermRun.Frame → MemSide isa) (fr : TermRun.Frame)
    (m0 : MachineData) (σC : AS) (Jp J1 J2 J3 J4 Jr Jw : AS → Ctl → Prop) : Prop where
  rd : RdPostW (fun s c => W s c [fr]) K exe endPc (mR R) (mF R F m0 σC) Jp J1 J2 J3 J4
  tl : MainX2W (fun s c => W s c []) K exe endPc R F (ms []) σC Jr Jw

section MainPostS

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`scc_rt_main` from `wc_rodata`'s `.x13` at depth**: from `.x13` in
`wc_rodata`'s region under the frame `fr` (no type variables, `hfr`) to
`print`'s abort with no frame. `wc_rodata`'s rest at `[fr]` under `ms [fr]`
(`hello1_rodata_post_segW` to `scc_rt_main`'s `.x2` of invariant
`retJ fr Jr`: `hbp`, `hra`, `hmem`, `h1` … `h4`, `hedge` as there), leaving
its region (`at_leave`; `%rbp` at the saved `%rbp`, `hbpr`) and returning
into `fr` (`FrameStep.ret`, `SegWS.post_run`); then `hello1_main_x2_segW`
at `[]` under `ms []` (`hK`, `hlimW`, `hsvc`, `hedgeW`, `hbpw`, `hok`). Its
states lie in `W`, none moved by `K` (`hW`). -/
theorem hello1_main_post_segWS {W : FragS isa} {K : State → State → Prop} {fr : TermRun.Frame}
    (hp : Lays exe SccCode.hello1Cells) (hend : endPc = endOf exe SccCode.hello1Cells)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -288) (hhi : 8 ≤ R.hi)
    (hK : (ms []).K = some Scc.Sem.X64.abi) (hfr : fr.σs = [])
    {m0 : MachineData} {σC : AS} {Jp J1 J2 J3 J4 Jr Jw : AS → Ctl → Prop}
    (hW : MainPostSW W K exe endPc R F ms fr m0 σC Jp J1 J2 J3 J4 Jr Jw)
    (hbp : ∀ σ0 c, Jp σ0 c → σ0.regs.get64 .rbp = (mR R).addr (-8))
    (hra : ∀ σ0 c, Jp σ0 c → (_root_.Executable.labels exe).label ".Lscc_rt_main.x2" = Int64.ofBitVec (σ0.slot 0))
    (hmem : ∀ σ0 c, Jp σ0 c → ∀ i : Int64, (i = 0 ∨ i = 8) →
      ∀ m, mF R F m0 σC m → Mem.loadInt m.dmem (bAddr σ0.regs .rax i) 8 = none)
    (h1 : ∀ σ0 c, Jp σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (bAddr σ0.regs .rax 0).toNat ∧ c.hold = none ∧
      ∀ (r : Val) (w' : TermRun.Word), (ms [fr]).rd w' → Scc.Sem.ValRep lbl w'.val (r.setWidth 64).toNat →
        J1 σ0 { c with hold := some ((bAddr σ0.regs .rax 0).toNat, w') })
    (h2 : ∀ σ0 c, J1 σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr) (tv : Ty)
      (wv wold : TermRun.Word),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (bAddr σ0.regs .rax 0).toNat ∧
      c.hold = some ((bAddr σ0.regs .rax 0).toNat, wold) ∧ TermRun.evalAt c.env v = some (tv, [wv]) ∧
      Scc.Sem.ValRep lbl wv.val (rpK1.setWidth 128).toNat ∧ J2 σ0 ⟨e, (x, u, [wold]) :: c.env, none⟩)
    (h3 : ∀ σ0 c, J2 σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (bAddr σ0.regs .rax 8).toNat ∧ c.hold = none ∧
      ∀ (r : Val) (w' : TermRun.Word), (ms [fr]).rd w' → Scc.Sem.ValRep lbl w'.val (r.setWidth 64).toNat →
        J3 σ0 { c with hold := some ((bAddr σ0.regs .rax 8).toNat, w') })
    (h4 : ∀ σ0 c, J3 σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr) (tv : Ty)
      (wv wold : TermRun.Word),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (bAddr σ0.regs .rax 8).toNat ∧
      c.hold = some ((bAddr σ0.regs .rax 8).toNat, wold) ∧ TermRun.evalAt c.env v = some (tv, [wv]) ∧
      Scc.Sem.ValRep lbl wv.val (rpK2.setWidth 128).toNat ∧ J4 σ0 ⟨e, (x, u, [wold]) :: c.env, none⟩)
    (hedge : ∀ σ0 c, J4 σ0 c → ∀ σ' : AS, σ'.regs.rax.toBitVec = σ0.regs.rax.toBitVec →
      σ'.regs.rdx.toBitVec = 0#64 → σ'.regs.rcx.toBitVec = 2#64 → σ'.regs.rsi.toBitVec = 13#64 →
      σ'.regs.rbp.toBitVec = σ0.slot (-8) → σ'.regs.rsp.toBitVec = σ0.regs.rbp.toBitVec + 8#64 + 8#64 →
      ∃ c', LocalRun p c c' ∧ retJ fr Jr σ' c')
    (hbpr : ∀ σx c, Jr σx c → σx.regs.get64 .rbp = R.addr (-8))
    (hlimW : ∀ σx c, Jr σx c → LimOk (ms []) F (σx.regs.fsBase.toBitVec + (8 : Int64).toBitVec)
      (σx.regs.rsp.toBitVec - 8#64 - 8#64 - (80 : Int64).toBitVec))
    (hsvc : ∀ F' : MachineData → Prop, FStable (pR (wR R)) F' →
      (∀ m, F' m → ((F m ∧ CallerCells R (-80) (-144) 8 m) ∧ CallerCells (wR R) (-96 - 8) (-40) 16 m) ∧
        Spike.Lib.X64.Rt.WcRa (wR R) ((_root_.Executable.labels exe).label ".Lscc_rt_main.x3") m ∧
        Spike.Lib.X64.Rt.WcFp (wR R) (R.addr (-8)) m) →
      ∀ g' : PG, g'.2.2 = ((_root_.Executable.labels exe).label ".Lwc_main.x15").toBitVec →
      g'.2.1 = (wR R).addr (-8) →
      SegW (fun s c => W s c []) K p lbl (ms [])
        (At exe endPc (pR (wR R)) F' (Print.N (_root_.Executable.labels exe).label g'.1 g'.2.1 g'.2.2 .sys))
        (At exe endPc (pR (wR R)) F' (Print.N (_root_.Executable.labels exe).label g'.1 g'.2.1 g'.2.2 .n5)))
    (hedgeW : ∀ g : AS × Ctl, ∀ σ c, wcJ (wJ0 (_root_.Executable.labels exe).label σC Jr g) σ c →
      σ.regs.get64 .rbp = (wR R).addr (-8) → ∀ σ' : AS,
      (∀ k, -88 ≤ k → k < 8 → k % 8 = 0 → σ'.slot k = wcSl (_root_.Executable.labels exe).label σ k) →
      σ'.regs.rax.toBitVec = 0#64 → σ'.regs.rbp.toBitVec = σ.slot (-8) →
      σ'.regs.rsp.toBitVec = σ.regs.rbp.toBitVec + 8#64 + 8#64 →
      ∃ c', LocalRun p c c' ∧ Jw σ' c')
    (hbpw : ∀ σx c, Jw σx c → σx.regs.get64 .rbp = R.addr (-8))
    (hok : ∀ s c σx, Jw σx c →
      At exe endPc R F ⟨(_root_.Executable.labels exe).label ".Lscc_rt_main.x3" + Int64.ofNat 4 + Int64.ofNat 4 +
        Int64.ofNat 5, mO, fun _ _ => True⟩ s c → SysOk p (ms []) s c (.exitGroup σx.regs.rax.toNat)) :
    SegWS W K p lbl ms
      ((At exe endPc (mR R) (mF R F m0 σC) (rdX13 (_root_.Executable.labels exe).label Jp)).at [fr])
      ((At exe endPc R F (mAb (_root_.Executable.labels exe).label)).at []) := by
  let lab := (_root_.Executable.labels exe).label
  obtain ⟨hR', hF'⟩ := mR_ok hR hF hlo hhi m0 σC
  refine SegWS.seq (Q := (At exe endPc R F (mS0 lab R σC Jr)).at []) (SegWS.post_run ?_)
    (SegWS.liftS [] (hello1_main_x2_segW hp hend hF hR hlo hhi hK hW.tl hbpr hlimW hsvc hedgeW hbpw hok)
      fun _ _ h => h)
  refine (SegWS.liftS [fr] (hello1_rodata_post_segW hp hend hF' hR' (by show (-208 : Int) ≤ -40; decide)
    (by show (8 : Int) ≤ 8; decide) (x := ⟨lab ".Lscc_rt_main.x2", ⟨8, []⟩, retJ fr Jr⟩) rfl hW.rd hbp hra
    hmem h1 h2 h3 h4 hedge) fun _ _ h => h).mono_post ?_
  rintro s c fs ⟨h, rfl⟩
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, σx, σC', ⟨a, t, ws, hc, ha, hJ⟩, rfl, hσ⟩ :=
    at_leave (P := fun σ => σ = σC) rfl (fun m hm => ⟨hm.1, m0, σC, ⟨-80, []⟩, hm.2.1, hm.2.2, rfl⟩) h
  refine ⟨_, [], .single (FrameStep.ret hc hfr ha), ?_, rfl⟩
  refine At.rbp_addr (J := (mS0 lab R σC' Jr).J) ⟨he, hn, hdc, hpc, σ, hA, hD, σx, hJ, hσ⟩ ?_
  rintro σ c ⟨σx, hJ, rfl⟩
  exact hbpr σx c hJ

end MainPostS

end Spike.Lib.X64.Flow.Hello1
