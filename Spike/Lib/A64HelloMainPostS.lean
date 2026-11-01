/-
**`hello.w`'s `scc_rt_main` from `wc_rodata`'s allocator's return at depth** (AArch64,
Option A): `HelloM.hello_main_post_segW` over segments with frames (`SegWS`, `Spike/Lib/SegS.lean`),
`wc_rodata` under the frame its source call pushed (`HelloRdCf.frH env`, the setup block's call of `rodata`).
The twin at hello of `Hello1.hello1_main_post_segWS` (`Spike/Lib/A64Hello1SetupPost.lean`).

`hello_main_post_segW` runs `wc_rodata`'s rest and `scc_rt_main`'s rest as one frameless segment, the source's
return out of `rodata` a local run (`hedge` into `Jr`): at the real run (the setup start, `rodata` called)
no local run leaves `rodata`'s `ret`, so `hedge` holds only for an empty `J5`. Here `rodata`'s return pops the
frame `fr`: `wc_rodata`'s rest is a segment at `[fr]` (`SegWS.liftS`), its exit at `.sp0` a pair whose source
is at `ret a` with `fr`'s continuation of invariant `Jr` (`HelloRdCf.retJH`), the return taken with the row
that lands there (`FrameStep.ret`, `SegWS.post_run`); `scc_rt_main`'s rest (the `.sp0` block, the call of
`wc_main`, `wc_main`'s segment `hWc`) is a segment at `[]`.

- `MainPostSWH`: `wc_rodata`'s states from `.sp0` at `[fr]`, the `.sp0` block's at `[]`.
- `hello_main_sp0_segW`: `scc_rt_main` from `.sp0` (of `wc_rodata`'s return invariant `Jr`, left its region)
  into `wc_main`'s segment, frameless (`hello_main_post_segW`'s second part).
- `hello_main_post_segWS`: from `wc_rodata`'s `.sp0` at `[fr]` to `wc_main`'s segment's exits at `[]`.
-/
import Spike.Lib.A64HelloMain
import Spike.Lib.A64HelloRdCf
import Spike.Lib.SegS

namespace Spike.Lib.A64.Flow.HelloM

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (CallerCells LimOk seg_oneW)
open Spike.Lib.A64.Flow.Hello1 (mB1 mB1_ok mB1_run mainIn mR mF mR_ok mS0 mWC rpK1 rpK2)
open Spike.Lib.A64.Flow.HelloRd (RdPostW pN hello_rodata_post_runW)
open Spike.Lib.HelloRdCf (retJH)
open Scc.Cert.Rt.A64 (Lays endOf label_labelGap)

set_option linter.unusedSimpArgs false

/-! ## `scc_rt_main` from `.sp0`, frameless -/

section MainSp0

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`scc_rt_main` from `.sp0` into `wc_main` is one segment inside `W`** in any valid layout of `helloProg`,
for a caller's state `σC` at `wc_rodata`'s call: from `.sp0` (`wc_rodata`'s return of invariant `Jr`, left its
region), the `.sp0` block (`hsp0`), the call of `wc_main` into its region at the call (`D` deep, `at_enter`),
then `wc_main`'s segment there (`hWc`), as in `hello_main_post_segW`. -/
theorem hello_main_sp0_segW {W : Frag isaLSE2} {K : State → State → Prop}
    {kp : Nat} (hp : Lays exe SccCode.helloProg kp) (hend : endPc = endOf exe SccCode.helloProg kp)
    {D : Int} (hD : 0 ≤ D) (hD16 : D % 16 = 0)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -288) (hloD : R.lo ≤ -80 - D)
    (hhi : 0 ≤ R.hi) {σC : AS} {Jr : AS → Ctl → Prop}
    (hsp0 : BlkW W K exe endPc R F (mS0 (_root_.Executable.labels exe).label R σC Jr) mB1)
    {Q : MachineData → AS → Frag isaLSE2}
    (hWc : ∀ m1 σ1, (wcR R D).OK → (wcR R D).base.toNat % 16 = 0 → FStable (wcR R D) (wcF R D F m1 σ1) →
      SegW W K p lbl ms (At exe endPc (wcR R D) (wcF R D F m1 σ1)
        ⟨(_root_.Executable.labels exe).label "wc_main", ⟨0, []⟩,
          wcJ0 (mWC (_root_.Executable.labels exe).label σC Jr).J σ1⟩) (Q m1 σ1)) :
    SegW W K p lbl ms (At exe endPc R F (mS0 (_root_.Executable.labels exe).label R σC Jr))
      (fun s c => ∃ m1 σ1, Q m1 σ1 s c) := by
  let lab := (_root_.Executable.labels exe).label
  have hin := hello_mainIn
  simp only [mainIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨-, hb1⟩, -⟩, hg2⟩ := hin
  have e2 : lab ".L1_scc_rt_main.sp1" = lab ".L1_scc_rt_main.sp0" + Int64.ofNat (4 * 10) :=
    label_labelGap hp hg2
  refine SegW.seq (Q := At exe endPc R F (mWC lab σC Jr))
    (seg_oneW (seg_ndW (by simp [mB1]) mB1_ok hF hR hal (by omega) hhi
      (code_of hp hend hb1 (ofNat4_zero _)) hsp0 fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)) ?_
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
  · -- `wc_main` in its region
    refine SegW.mono_pre (P := fun s c => ∃ G : MachineData × AS, At exe endPc (wcR R D) (wcF R D F G.1 G.2)
      ⟨lab "wc_main", ⟨0, []⟩, wcJ0 (mWC lab σC Jr).J G.2⟩ s c) (SegW.exists_pre fun G => ?_) ?_
    · obtain ⟨hR'', hal'', hF''⟩ := wcR_ok hD hD16 hR hal hF hloD hhi G.1 G.2
      exact (hWc G.1 G.2 hR'' hal'' hF'').mono_post fun s c h => ⟨G.1, G.2, h⟩
    · intro s c h
      obtain ⟨m1, σ1, he, hn, hdc, hpc, σ, hA, hD', hc, hσ, hJ⟩ := at_enter (lo' := -D) (hi' := 0)
        (by show R.lo ≤ -80 + -D; omega) (by show (-80 : Int) < R.hi; omega) (by decide)
        (by show (-80 : Int) % 8 = 0; decide) h
      exact ⟨(m1, σ1), he, hn, hdc, hpc, σ, hA, hD', hσ, hc ▸ hJ⟩

end MainSp0

/-! ## `wc_rodata`'s return pops the setup frame -/

/-- **`scc_rt_main`'s states from `wc_rodata`'s `.sp0` with frames**: `wc_rodata`'s under the frame `fr` its
source call pushed, the `.sp0` block's with none (`MainPostW` split by frames). -/
structure MainPostSWH (W : FragS isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (fr : TermRun.Frame) (m0 : MachineData) (σC : AS)
    (Jp Jp' J1 J2 J2' J3 J4 J5 Jr : AS → Ctl → Prop) : Prop where
  rd : RdPostW (fun s c => W s c [fr]) K exe endPc (mR R) (mF R F m0 σC) Jp Jp' J1 J2 J2' J3 J4 J5
  sp0 : BlkW (fun s c => W s c []) K exe endPc R F (mS0 (_root_.Executable.labels exe).label R σC Jr) mB1

section MainPostS

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`scc_rt_main` from `wc_rodata`'s `.sp0` into `wc_main` at depth**: from `.sp0` in `wc_rodata`'s region
under the frame `fr` (no type variables, `hfr`) to `wc_main`'s segment's exits with no frame. `wc_rodata`'s rest
at `[fr]` under `ms [fr]` (`hello_rodata_post_runW` to `scc_rt_main`'s `.sp0` of invariant `retJH fr Jr`:
`hra` … `hfen`, `hedge` as there), leaving its region (`at_leave`) and returning into `fr` (`FrameStep.ret`,
`SegWS.post_run`); then `hello_main_sp0_segW` at `[]` under `ms []` (`hWc`). Its states lie in `W`, none moved
by `K` (`hW`). -/
theorem hello_main_post_segWS {W : FragS isaLSE2} {K : State → State → Prop} {fr : TermRun.Frame}
    {kp : Nat} (hp : Lays exe SccCode.helloProg kp) (hend : endPc = endOf exe SccCode.helloProg kp)
    {D : Int} (hD : 0 ≤ D) (hD16 : D % 16 = 0)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -288) (hloD : R.lo ≤ -80 - D)
    (hhi : 0 ≤ R.hi) (hfr : fr.σs = []) {m0 : MachineData} {σC : AS}
    {Jp Jp' J1 J2 J2' J3 J4 J5 Jr : AS → Ctl → Prop}
    (hW : MainPostSWH W K exe endPc R F fr m0 σC Jp Jp' J1 J2 J2' J3 J4 J5 Jr)
    (hra : ∀ σ0 c, Jp σ0 c → (_root_.Executable.labels exe).label ".L1_scc_rt_main.sp0" = Int64.ofBitVec (σ0.slot (-8)))
    (hmem : ∀ σ0 c, Jp σ0 c → ∀ i : Int64, (i = 0 ∨ i = 8) →
      ∀ m, mF R F m0 σC m → Mem.loadInt m.dmem (rAddr σ0.regs .X0 i) 8 = none)
    (hr0 : ∀ σ0 c, Jp σ0 c → ∃ c', LocalRun p c c' ∧ Jp' σ0 c')
    (h1 : ∀ σ0 c, Jp' σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (rAddr σ0.regs .X0 0).toNat ∧ c.hold = none ∧
      ∀ (r : Val) (w' : TermRun.Word), (ms [fr]).rd w' → Scc.Sem.ValRep lbl w'.val (r.setWidth 64).toNat →
        J1 σ0 { c with hold := some ((rAddr σ0.regs .X0 0).toNat, w') })
    (h2 : ∀ σ0 c, J1 σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr) (tv : Ty)
      (wv wold : TermRun.Word),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (rAddr σ0.regs .X0 0).toNat ∧
      c.hold = some ((rAddr σ0.regs .X0 0).toNat, wold) ∧ TermRun.evalAt c.env v = some (tv, [wv]) ∧
      Scc.Sem.ValRep lbl wv.val (rpK1.setWidth 128).toNat ∧ J2 σ0 ⟨e, (x, u, [wold]) :: c.env, none⟩)
    (hr2 : ∀ σ0 c, J2 σ0 c → ∃ c', LocalRun p c c' ∧ J2' σ0 c')
    (h3 : ∀ σ0 c, J2' σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (rAddr σ0.regs .X0 8).toNat ∧ c.hold = none ∧
      ∀ (r : Val) (w' : TermRun.Word), (ms [fr]).rd w' → Scc.Sem.ValRep lbl w'.val (r.setWidth 64).toNat →
        J3 σ0 { c with hold := some ((rAddr σ0.regs .X0 8).toNat, w') })
    (h4 : ∀ σ0 c, J3 σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr) (tv : Ty)
      (wv wold : TermRun.Word),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (rAddr σ0.regs .X0 8).toNat ∧
      c.hold = some ((rAddr σ0.regs .X0 8).toNat, wold) ∧ TermRun.evalAt c.env v = some (tv, [wv]) ∧
      Scc.Sem.ValRep lbl wv.val (rpK2.setWidth 128).toNat ∧ J4 σ0 ⟨e, (x, u, [wold]) :: c.env, none⟩)
    (hfen : ∀ σ0 c, J4 σ0 c → ∃ c', FenceRun p (ms [fr]).pub .st c c' ∧ J5 σ0 c')
    (hedge : ∀ σ0 c, J5 σ0 c → ∀ σ' : AS, σ'.regs.X0.toBitVec = σ0.regs.X0.toBitVec →
      σ'.regs.X1.toBitVec = 0#64 → σ'.regs.X2.toBitVec = 2#64 → σ'.regs.X3.toBitVec = 13#64 →
      σ'.regs.X29.toBitVec = σ0.slot (-16) → σ'.regs.X30.toBitVec = σ0.slot (-8) →
      ∃ c', LocalRun p c c' ∧ retJH fr Jr σ' c')
    {Q : MachineData → AS → Frag isaLSE2}
    (hWc : ∀ m1 σ1, (wcR R D).OK → (wcR R D).base.toNat % 16 = 0 → FStable (wcR R D) (wcF R D F m1 σ1) →
      SegW (fun s c => W s c []) K p lbl (ms []) (At exe endPc (wcR R D) (wcF R D F m1 σ1)
        ⟨(_root_.Executable.labels exe).label "wc_main", ⟨0, []⟩,
          wcJ0 (mWC (_root_.Executable.labels exe).label σC Jr).J σ1⟩) (Q m1 σ1)) :
    SegWS W K p lbl ms
      ((At exe endPc (mR R) (mF R F m0 σC)
        (pN (_root_.Executable.labels exe).label Jp Jp' J1 J2 J2' J3 J4 J5 .s0)).at [fr])
      (Frag.at (fun s c => ∃ m1 σ1, Q m1 σ1 s c) []) := by
  let lab := (_root_.Executable.labels exe).label
  obtain ⟨hR', hal', hF'⟩ := mR_ok hR hal hF hlo hhi m0 σC
  refine SegWS.seq (Q := (At exe endPc R F (mS0 lab R σC Jr)).at []) (SegWS.post_run ?_)
    (SegWS.liftS [] (hello_main_sp0_segW hp hend hD hD16 hF hR hal hlo hloD hhi hW.sp0 hWc) fun _ _ h => h)
  refine (SegWS.liftS [fr] (hello_rodata_post_runW hp hend hF' hR' hal' (by show (-208 : Int) ≤ -48; decide)
    (by show (0 : Int) ≤ 0; decide) (x := ⟨lab ".L1_scc_rt_main.sp0", ⟨0, []⟩, retJH fr Jr⟩) rfl hW.rd hra hmem
    hr0 h1 h2 hr2 h3 h4 hfen hedge) fun _ _ h => h).mono_post ?_
  rintro s c fs ⟨h, rfl⟩
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD', σx, σC', ⟨a, t, ws, hc, ha, hJ⟩, rfl, hσ⟩ :=
    at_leave (P := fun σ => σ = σC) rfl (fun m hm => ⟨hm.1, m0, σC, ⟨-80, []⟩, hm.2.1, hm.2.2, rfl⟩) h
  exact ⟨_, [], .single (FrameStep.ret hc hfr ha), ⟨he, hn, hdc, hpc, σ, hA, hD', σx, hJ, hσ⟩, rfl⟩

end MainPostS

end Spike.Lib.A64.Flow.HelloM

/-- info: 'Spike.Lib.A64.Flow.HelloM.hello_main_sp0_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloM.hello_main_sp0_segW

/--
info: 'Spike.Lib.A64.Flow.HelloM.hello_main_post_segWS' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloM.hello_main_post_segWS
