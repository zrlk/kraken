/-
**The heap abort's control facts at `wXA`, `c0H` placed from `wc_main`'s spills** (AArch64): at level 1 the
allocator's control `c0H` holds rodata's slice word
`loc ⟨l, 0⟩` at a dynamic base, so it is placed only where that base is. `HelloWc.wXA` (the heap abort with
`wc_main`'s spilled argument words `x0`–`x4` at its slots `-144 … -112`) records where: on the abort path (region
`R.callee (-304) (-48) 0`) those slots are outside the callee's window, kept from the caller's memory `m0`
(`CKept`), there the abstraction `σ`'s (`Abs`), and `σ`'s are the call's entry registers.

Copies (no edit) of `HAbStub.WcHAbStubH`, `HAbStub.wc_heapAb_segWSH`, `HabCtlS.HabCtlHS` and
`HabCtlS.wc_heapAbStubKHS` at `wXA`; the level-0 originals at `wXH .abort` stay.

- `WcHAbStubHA`, `wc_heapAb_segWSHA`: the heap abort's obligations and its segment with no return, at `wXA`.
- `HabCtlHA`: the control facts at `wXA` with the placement under the path's frame condition.
- `wc_heapAbStubKHA`: `WcHAbStubHA` under `PhRec.K` from `HabCtlHA`.
- `placeVal_slot_keptA`: a slot of `wc_main`'s frame at or above `-304` on the abort path is `σ`'s.
- `placedSE_c0H`: `c0H` on a slice at `l` placed at four slots (`z` immediate).
- `habCtlHA_c0H`: `HabCtlHA` below `wc_main`'s entry whose caller's controls are `c0H` on the slice at `l` in
  `x0`–`x3` (`SlRegs`) and main's id at the caller's slot `-80` (`hmt`); no placement premise.
- `hmt_HA`: main's id at its TCB at `upd LB l b` (copy of `Box.hmt_H`).
- `habCtlHA_jr1L`: at level 1's `Land.Jr1LH hpw i0 l b`, from `l` fresh, the caller's slot `-80` main's TCB and the
  certificate table's `z` (`hz`); `hz_i0M`: `hz` at the root's `ImmsMe.i0M`.
-/
import Spike.Lib.A64HelloHabCtlS
import Spike.Lib.A64HelloHabCtlC0
import Spike.Lib.A64HelloWcPreA
import Spike.Lib.A64HelloImmsMe

namespace Spike.Lib.A64.HelloPh.HabCtlA

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Link.A64 (codeOf)
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf abi)
open Spike.Lib (Arena FragS Frag Region HeapAbortOblA SegWS Ctl)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64ConsumerS (PlacedSE)
open Spike.Lib.A64.Flow (ND At)
open Spike.Lib.A64.WakeWf (DtW W0 RunWf)
open Spike.Lib.A64.Flow.HelloWc (wXA)
open Spike.Lib.A64.Flow.Hello1 (mWC)
open Spike.Lib.A64.Flow.HelloM (wcJ0)
open Spike.Lib.A64.Flow.HelloJr1 (SlRegs)
open Spike.Lib.A64.Flow.Worker.Hello.Child (pfxM)
open Spike.Lib.A64.HelloPh (lo ownGH)
open Spike.Lib.A64.HelloPh.HAbStub (hpathW_hXH abort_offH)
open Spike.Lib.HelloMainPreSrc (c0H c0H_term boxTermH newTerm)
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.WakeT1 (mainTidLbl)
open Spike.Lib.WakeSrcCtl (placedSE_of_tbl rep_at)

set_option linter.unusedSimpArgs false

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.A64.Flow.AS

/-! ## The heap abort at `wXA` -/

section Tail

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **The heap abort's obligations at `wXA`** (`WcHAbStubH`'s twin): the heap abort path's below `-304` for every
caller's state and source control of `wXA`. -/
def WcHAbStubHA (W : FragS isaLSE2) (K : State → State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (ms : List TermRun.Frame → MemSide isaLSE2) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (fs : List TermRun.Frame) (J1 : FAS → Ctl → Prop) : Prop :=
  ∀ m0 σC c0, (wXA (ms fs) (_root_.Executable.labels exe).label J1).J σC c0 →
    Abort.Disp.StubHRW (fun s c => W s c fs) K p lbl (ms fs) exe endPc (R.callee (-304) (-48) 0)
      (fun m => F m ∧ Flow.CKept R (-304) (-48) 0 m0 m ∧ Flow.Abs R ⟨-304, []⟩ m0 σC) c0
      ((_root_.Executable.labels exe).label ".L2_scc_rt_alloc.4_full" + 8).toBitVec

/-- **The heap abort at `wXA` does not return** (`wc_heapAb_segWSH`'s twin, `seg_jabort2RW` at `-304`). -/
theorem wc_heapAb_segWSHA {W : FragS isaLSE2} {K : State → State → Prop} {fs : List TermRun.Frame}
    {J1 : FAS → Ctl → Prop}
    (hF : Flow.FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -352) (hhi : 0 ≤ R.hi)
    (hK : (ms fs).K = some Scc.Sem.A64.abi) (hstub : WcHAbStubHA W K p lbl ms exe endPc R F fs J1)
    (Q : FragS isaLSE2) :
    SegWS W K p lbl ms ((At exe endPc R F (wXA (ms fs) (_root_.Executable.labels exe).label J1)).at fs) Q :=
  SegWS.liftS_noret fs (Abort.Disp.seg_jabort2RW (Q := fun _ _ => False)
    (nC := wXA (ms fs) (_root_.Executable.labels exe).label J1) rfl
    (fun σ c h => by show σ.regs.X0.toBitVec.toNat = 2; rw [h.1]; rfl) (fun σ c h => h.2.1)
    hF hR hal (by show R.lo ≤ -304 - 48; omega) (by show (-304 : Int) < R.hi; omega)
    (by show (-304 : Int) % 16 = 0; decide) hK hstub) (fun _ _ h => h) Q

end Tail

/-- **The control facts at `wXA` with the placement on the path** (`HabCtlHS`'s twin at `wXA`): `c0` placed at
the states whose memory meets `F` and keeps the caller's region above the callee's window from `m0`, abstracted
by `wXA`'s `σ`. -/
def HabCtlHA (ms : Spike.Lib.MemSide isaLSE2) (lab : String → Int64) (p : Prog) (Λ : Scc.Sem.Layout) (L0 : Lbl)
    (ar : Arena) (fs : List TermRun.Frame) (J1 : FAS → Ctl → Prop) (R : Region)
    (F : MachineData → Prop) : Prop :=
  ∀ σ c0, (wXA ms lab J1).J σ c0 →
    ((fs = [] → ∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 fs) ∧
      (∀ m0 (s : State), F s.st.1 → Flow.CKept R (-304) (-48) 0 m0 s.st.1 →
        Flow.Abs R ⟨-304, []⟩ m0 σ → PlacedSE Λ L0 s c0 fs) ∧
      HeapAbortOblA ar.cells ar.ctr c0

section Inst

variable {L : RuntimeLayout}
variable (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo)
  (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
include hp hlo hlab

/-- **`WcHAbStubHA` from `HabCtlHA`** (`wc_heapAbStubKHS`'s twin at `wXA`). -/
theorem wc_heapAbStubKHA {R : Region} {F : MachineData → Prop} {ar : Arena} {p : Prog} {Cl : State → Prop}
    {Ctx : FragS isaLSE2} {L0 : Lbl} {ls0 : Lsize} {frM : TermRun.Frame} {X0 : State → Prop}
    {fs : List TermRun.Frame} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
    {J1 : FAS → Ctl → Prop} {rS : Scc.Sem.Range} (a : BitVec 64)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hF : Flow.FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo' : R.lo ≤ -352)
    (hhi : 0 ≤ R.hi) (hK : (ms fs).K = some abi) (hfs : fs = [] ∨ fs = [frM])
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hctl : HabCtlHA (ms fs) L.lab p L.Λ L0 ar fs J1 R F)
    (hab : ∀ s : State, s.st.2 = L.lab "scc_rt_abort_heap_exit" → (ms fs).abortAt s)
    (hX0 : ∀ s, Spike.Lib.A64.WakePh.inPc L "scc_rt_abort" "scc_rt_thr_worker" s → X0 s) :
    WcHAbStubHA (W0 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) ar p DtW (Spike.Lib.A64.WriteAb.Ab L.lab) Cl
      (Spike.Lib.A64.HelloWf.AcH L.lab pfxM) Ctx L0 ls0 frM X0) (Spike.Lib.A64.PhRec.K L rS) p lbl ms L.exe
      L.endPc R F fs J1 := by
  intro m0 σC c0 hJ
  obtain ⟨hc0, hpl, hobl⟩ := hctl σC c0 hJ
  have hkc : (-304 : Int) < R.hi := by omega
  have hF' : Flow.FStable (R.callee (-304) (-48) 0) (fun m => F m ∧
      Flow.CKept R (-304) (-48) 0 m0 m ∧ Flow.Abs R ⟨-304, []⟩ m0 σC) :=
    Flow.fstable_enter hR hF (by omega) (by decide) hkc (by decide) (by omega) (by decide) (by decide)
  have hb := Region.callee_base (hi' := 0) hR (show R.lo ≤ -304 + -48 by omega) (by decide) hkc
  have hal' : (R.callee (-304) (-48) 0).base.toNat % 16 = 0 := by
    have : (((R.callee (-304) (-48) 0).base.toNat : Int)) % 16 = 0 := by rw [hb]; omega
    omega
  have hR' := Region.callee_ok (hi' := 0) hR (show R.lo ≤ -304 + -48 by omega) (by decide) hkc (by omega)
  have h0 := HabCtlS.hpathW_hab0HS (ar := ar) (p := p) (Cl := Cl) (Ctx := Ctx) (L0 := L0) (ls0 := ls0)
    (frM := frM) (X0 := X0) (F := fun m => F m ∧ Flow.CKept R (-304) (-48) 0 m0 m ∧
      Flow.Abs R ⟨-304, []⟩ m0 σC) hp hlo hlab a hΛ hR' hal'
    (by simp [Region.callee]) (by simp [Region.callee]) rfl hfs hcl hc0 hF'
    (fun s h => hpl m0 s h.1 h.2.1 h.2.2) hobl hX0
  have hX := hpathW_hXH (F := fun m => F m ∧ Flow.CKept R (-304) (-48) 0 m0 m ∧
      Flow.Abs R ⟨-304, []⟩ m0 σC) (c0 := c0)
    (ra := (L.lab ".L2_scc_rt_alloc.4_full" + 8).toBitVec) hlab hR' hal' (by simp [Region.callee])
    (by simp [Region.callee]) hp hlo
  have hpath := Spike.Lib.A64.WakePh.HPathW.map (Spike.Lib.A64.WakePh.HAbStubK.hpathW_K
    (K := Spike.Lib.A64.PhRec.K L rS)
    (Abort.Disp.HPathW.and h0 hX fun _ _ h₁ h₂ => And.intro h₁ h₂)
    fun s _ h s' hk => (abort_offH hlab s h.2).2 (congrArg (fun x : Int64 => x.toBitVec.toNat) hk.1))
    fun _ _ h => h.1
  exact Spike.Lib.A64.StubW.stubHRW_of_code L.lays rfl (hp ▸ SccCode.hello_abort) hK hF' hpath
    fun s _ ⟨_, _, _, hpc, _⟩ => hab s hpc

end Inst

/-! ## `c0H` placed from the spills -/

/-- **A slot of `wc_main`'s frame on the abort path**: at or above `-304` it is outside the callee's window, so
as in the caller's memory `m0` (`CKept`), there `σ`'s (`Abs`). -/
theorem placeVal_slot_keptA {R : Region} {m0 : MachineData} {σ : FAS} {s : State}
    (hA : Flow.Abs R ⟨-304, []⟩ m0 σ) (hK : Flow.CKept R (-304) (-48) 0 m0 s.st.1) {k : Int} (hk : R.Off k)
    (hk' : -304 ≤ k) :
    Scc.Sem.placeVal (Scc.Sem.A64.machine (Scc.Sem.A64.kernel 1)) s (.slot (R.addr k).toNat) =
      some (σ.slot k).toNat := by
  obtain ⟨j, hj, hv⟩ := hA.slot k hk
  have hc : ¬ (R.callee (-304) (-48) 0).Off (k - -304) := fun ⟨_, _, h3⟩ => by
    simp only [Region.callee] at h3; omega
  show (Scc.Sem.A64.privLoad s (BitVec.ofNat 64 (R.addr k).toNat)).map (·.toNat) = _
  simp [Scc.Sem.A64.privLoad, hK k hk hc, hj, hv]

/-- **`c0H` on the slice at `l` placed at four slots**: the base at `a0` (offset immediate `0`), `m`, `n` at `a2`,
`a3`, main's id at `am`; `z` the layout's immediate `0` at `newTerm` (`hiz`). -/
theorem placedSE_c0H {Λ : Scc.Sem.Layout} {lbl : Lbl} {s : State} {l : WeakMem.AllocLabel} (a0 a2 a3 am : Nat)
    (hiz : Λ.imms newTerm "z" 0 = some 0)
    (h0 : ∃ v, Scc.Sem.placeVal (Scc.Sem.A64.machine (Scc.Sem.A64.kernel 1)) s (.slot a0) = some v ∧ lbl l = some v)
    (h2 : Scc.Sem.placeVal (Scc.Sem.A64.machine (Scc.Sem.A64.kernel 1)) s (.slot a2) = some 2)
    (h3 : Scc.Sem.placeVal (Scc.Sem.A64.machine (Scc.Sem.A64.kernel 1)) s (.slot a3) = some 13)
    (hm : ∃ v, Scc.Sem.placeVal (Scc.Sem.A64.machine (Scc.Sem.A64.kernel 1)) s (.slot am) = some v ∧
      lbl (mainTidLbl 2) = some v) :
    PlacedSE Λ lbl s (c0H (TermRun.cst (.loc ⟨l, 0⟩ 0)) (TermRun.cst (.num 2)) (TermRun.cst (.num 13))
      Spike.Lib.A64.HelloPh.Land.mwH) [] := by
  refine placedSE_of_tbl [("z", [.imm 0]), ("sl", [.loc (.slot a0) (.imm 0), .one (.slot a2), .one (.slot a3)]),
    ("me", [.one (.slot am)])] ?_ ?_ ?_
  · intro x hx ty ws hl
    rw [show (c0H (TermRun.cst (.loc ⟨l, 0⟩ 0)) (TermRun.cst (.num 2)) (TermRun.cst (.num 13))
      Spike.Lib.A64.HelloPh.Land.mwH).term = newTerm from rfl,
      show Scc.Sem.exprFv newTerm = ["z", "sl", "me"] by decide] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> cases hl <;> exact ⟨_, rfl, by simp⟩
  · intro x pls ty ws hpl hl k wp wd hwp hwd
    by_cases ez : x = "z"
    · subst ez; cases hpl; cases hl
      match k, hwp, hwd with | 0, hwp, hwd => cases hwp; cases hwd; exact ⟨by decide, rfl⟩
    by_cases es : x = "sl"
    · subst es; simp [List.lookup] at hpl; subst hpl; cases hl
      obtain ⟨v, hv, hlv⟩ := h0
      match k, hwp, hwd with
      | 0, hwp, hwd => cases hwp; cases hwd; exact ⟨v, 0, hv, rfl, rfl, hlv, rfl⟩
      | 1, hwp, hwd => cases hwp; cases hwd; exact ⟨2, h2, by decide, rfl⟩
      | 2, hwp, hwd => cases hwp; cases hwd; exact ⟨13, h3, by decide, rfl⟩
    by_cases em : x = "me"
    · subst em; simp [List.lookup] at hpl; subst hpl; cases hl
      match k, hwp, hwd with | 0, hwp, hwd => cases hwp; cases hwd; exact rep_at hm
    · simp [List.lookup, beq_false_of_ne ez, beq_false_of_ne es, beq_false_of_ne em] at hpl
  · intro x pls k n hpl hn'
    by_cases ez : x = "z"
    · subst ez; cases hpl
      match k, hn' with | 0, hn' => cases hn'; exact hiz
    by_cases es : x = "sl"
    · subst es; simp [List.lookup] at hpl; subst hpl
      match k, hn' with
      | 0, hn' => cases hn'
      | 1, hn' => cases hn'
      | 2, hn' => cases hn'
    by_cases em : x = "me"
    · subst em; simp [List.lookup] at hpl; subst hpl
      match k, hn' with | 0, hn' => cases hn'
    · simp [List.lookup, beq_false_of_ne ez, beq_false_of_ne es, beq_false_of_ne em] at hpl

/-- **`HabCtlHA` below `c0H` on a slice at `l`** (row `5h-S-habctl-L1`; `HabCtlC0.habCtlH_c0H` at `wXA`, no
placement premise): below `wc_main`'s entry invariant whose caller's controls are `c0H` on the slice at `l` in
`x0`–`x3` (`hJr`, `SlRegs` at `L0`) with main's id at the caller's slot `-80` (`hmt`), the control is placed at
`wc_main`'s spills `-144`, `-128`, `-120`, `-112`, given the layout's `z` (`hiz`) and the arena facts. -/
theorem habCtlHA_c0H {ms : Spike.Lib.MemSide isaLSE2} {lab : String → Int64} {Λ : Scc.Sem.Layout} {L0 : Lbl}
    {ar : Arena} {σC σ1 : FAS} {Jr : FAS → Ctl → Prop} {l : WeakMem.AllocLabel} {R : Region}
    {F : MachineData → Prop}
    (hJr : ∀ σ c, Jr σ c → c = c0H (TermRun.cst (.loc ⟨l, 0⟩ 0)) (TermRun.cst (.num 2)) (TermRun.cst (.num 13))
      Spike.Lib.A64.HelloPh.Land.mwH ∧ SlRegs L0 l σ)
    (hmt : L0 (mainTidLbl 2) = some (σC.slot (-80)).toNat) (hctr : ms.ctr = ar.ctr)
    (hcells : ms.cells = ar.cells) (hu : ms.units 1 .int = 2) (hiz : Λ.imms newTerm "z" 0 = some 0)
    (hlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi) :
    HabCtlHA ms lab helloSrc Λ L0 ar [] (wcJ0 (mWC lab σC Jr).J σ1) R F := by
  rintro σ c0 ⟨-, -, q, hfull, σe, ⟨rfl, σx, hJ, e0, -, e2, e3, e4, -⟩, s0, -, s2, s3, s4⟩
  obtain ⟨hq, hx0, -, hx2, hx3⟩ := hJr σx _ hJ
  have hctl := Spike.Lib.WakeSrcCtl.new_ctl (p := helloSrc) (c0H_term (TermRun.cst (.loc ⟨l, 0⟩ 0))
    (TermRun.cst (.num 2)) (TermRun.cst (.num 13)) Spike.Lib.A64.HelloPh.Land.mwH)
  obtain ⟨T, ht⟩ := q.2.term; rw [hq, c0H_term] at ht
  obtain ⟨-, ha, -⟩ := Expr.let_.inj ht
  have hev := q.2.ev; rw [hq, ← (Op.new.inj ha).1] at hev
  have hz : TermRun.evalAt (c0H (TermRun.cst (.loc ⟨l, 0⟩ 0)) (TermRun.cst (.num 2)) (TermRun.cst (.num 13))
      Spike.Lib.A64.HelloPh.Land.mwH).env (.var "z") = some (.int, [TermRun.cst (.num 0)]) := rfl
  have hτ : q.1.τ = .int := by rw [hz] at hev; exact (Prod.mk.inj (Option.some.inj hev)).1.symm
  rcases hfull with ⟨-, hn⟩ | ⟨o, rfl, -, hlt⟩
  · rw [q.2.one] at hn; exact absurd hn (by decide)
  rw [q.2.one, hτ, hu] at hlt; rw [hq]
  have hoff : ∀ k : Int, k % 8 = 0 → -304 ≤ k → k + 8 ≤ 0 → R.Off k := fun k h1 h2 h3 => ⟨h1, by omega, by omega⟩
  refine ⟨⟨fun _ => hctl.1, Spike.Lib.A64.WakePh.WcWf.RunWf.hold hctl.2⟩, fun m0 s _ hK hA => ?_, fun old h => ?_⟩
  · have pv := fun k hk hk' => placeVal_slot_keptA (s := s) hA hK (k := k) hk hk'
    refine Spike.Lib.A64.WakePh.WcWf.PlacedSE.hold.2 (placedSE_c0H (R.addr (-144)).toNat
      (R.addr (-128)).toNat (R.addr (-120)).toNat (R.addr (-112)).toNat hiz ?_ ?_ ?_ ?_)
    · exact ⟨_, pv (-144) (hoff _ (by decide) (by decide) (by decide)) (by decide), by
      rw [s0]; show _ = some σ1.regs.X0.toBitVec.toNat; rw [e0]; exact hx0⟩
    · rw [pv (-128) (hoff _ (by decide) (by decide) (by decide)) (by decide), s2]
      show some σ1.regs.X2.toBitVec.toNat = _; rw [e2, hx2]
    · rw [pv (-120) (hoff _ (by decide) (by decide) (by decide)) (by decide), s3]
      show some σ1.regs.X3.toBitVec.toNat = _; rw [e3, hx3]
    · exact ⟨_, pv (-112) (hoff _ (by decide) (by decide) (by decide)) (by decide), by
      rw [s4]; show _ = some σ1.regs.X4.toBitVec.toNat; rw [e4]; exact hmt⟩
  · obtain ⟨hle, hw⟩ := h (.inr ⟨"o", .var "z", boxTermH, _, rfl⟩)
    have he := hw _ (by rw [← hctr]; rfl)
    have ho : o.toNat = old := by simpa [TermRun.cst, Promises.TVal.mk0] using he
    exact .inr ⟨"o", .var "z", _, .int, TermRun.cst (.num 0), ⟨_, rfl⟩, rfl, rfl, hle, by rw [← hcells]; omega⟩

/-- **main's id at its TCB** at `upd LB l b`, `l` fresh at `LB` (a copy of `Box.hmt_H`, which keeps this
file off `A64HelloBoxM`). -/
theorem hmt_HA {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
    (hpw : PlaceW pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat) {l : WeakMem.AllocLabel} {b : Nat}
    (hl : Spike.Lib.WakeLoadT.L0T (RuntimeLayout.ofPlaceW hpw (Spike.Lib.A64.HelloPh.C0S.immsH Λ0 i0)).Λ l = none) :
    Spike.Lib.A64ConsumerA.upd
        (Spike.Lib.WakeLoadT.L0T (RuntimeLayout.ofPlaceW hpw (Spike.Lib.A64.HelloPh.C0S.immsH Λ0 i0)).Λ) l b
        (mainTidLbl 2) =
      some ((RuntimeLayout.ofPlaceW hpw (Spike.Lib.A64.HelloPh.C0S.immsH Λ0 i0)).pinA.toNat + 8) := by
  have hp0 := Spike.Lib.PlaceW.pinA_toNat_ofPlaceW hpw (Spike.Lib.A64.HelloPh.C0S.immsH Λ0 i0)
  have hsm := (RuntimeLayout.ofPlaceW hpw (Spike.Lib.A64.HelloPh.C0S.immsH Λ0 i0)).words_small _
    (RuntimeLayout.ofPlaceW hpw (Spike.Lib.A64.HelloPh.C0S.immsH Λ0 i0)).pin_mem
  have hme : Spike.Lib.WakeLoadT.L0T (RuntimeLayout.ofPlaceW hpw (Spike.Lib.A64.HelloPh.C0S.immsH Λ0 i0)).Λ
      (mainTidLbl 2) = some ((RuntimeLayout.ofPlaceW hpw (Spike.Lib.A64.HelloPh.C0S.immsH Λ0 i0)).pinA.toNat + 8) := by
    simp only [Spike.Lib.WakeLoadT.L0T, Spike.Lib.A64ConsumerA.upd, ↓reduceIte, Spike.Lib.WakeLoadT.tcb0,
      Option.some.injEq]
    omega
  have hne : mainTidLbl 2 ≠ l := by intro h; rw [h, hl] at hme; cases hme
  show (if _ = l then _ else _) = _
  split
  · exact absurd ‹_› hne
  · exact hme

/-- **The certificate table's `z` at `newTerm`** through the root's `ImmsMe.i0M` (`helloImm_t1`'s entry). -/
theorem hz_i0M (Λ0 : Scc.Sem.Layout) : Spike.Lib.A64.HelloPh.ImmsMe.i0M Λ0 newTerm "z" 0 = some 0 := by
  rw [Spike.Lib.A64.HelloPh.ImmsMe.i0M_i0Rd fun h => absurd h.2.1 (by decide)]
  exact Spike.Lib.A64.HelloPh.ImmsRd.i0Rd_helloImms (by
    have hne : SccCode.helloImm_t1 ≠ SccCode.helloImm_t2 := fun h => absurd (Expr.let_.inj h).1 (by decide)
    rw [show newTerm = SccCode.helloImm_t1 from rfl]; simp [SccCode.helloImms, hne])

/-- **`HabCtlHA` at level 1** (row `5h-S-habctl-L1`): below `Land.Jr1LH hpw i0 l b` at the level's labels
`upd LB l b` (`l` fresh at `LB`, `hl`), the caller's slot `-80` main's TCB (`hslot`, `HelloH2G.GJ1H`'s), the
certificate table's `z` (`hz`; at the root `hz_i0M`) and the arena facts. -/
theorem habCtlHA_jr1L {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
    (hpw : PlaceW pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat) {l : WeakMem.AllocLabel} {b : Nat}
    {ms : Spike.Lib.MemSide isaLSE2} {lab : String → Int64} {ar : Arena} {σC σ1 : FAS} {R : Region}
    {F : MachineData → Prop}
    (hl : Spike.Lib.WakeLoadT.L0T (RuntimeLayout.ofPlaceW hpw (Spike.Lib.A64.HelloPh.C0S.immsH Λ0 i0)).Λ l = none)
    (hslot : σC.slot (-80) =
      Spike.Lib.A64.Flow.Ret0.pinA (RuntimeLayout.ofPlaceW hpw (Spike.Lib.A64.HelloPh.C0S.immsH Λ0 i0)).lab +
        0#64 + 8#64)
    (hz : i0 newTerm "z" 0 = some 0) (hctr : ms.ctr = ar.ctr) (hcells : ms.cells = ar.cells)
    (hu : ms.units 1 .int = 2) (hlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi) :
    HabCtlHA ms lab helloSrc (RuntimeLayout.ofPlaceW hpw (Spike.Lib.A64.HelloPh.C0S.immsH Λ0 i0)).Λ
      (Spike.Lib.A64ConsumerA.upd
        (Spike.Lib.WakeLoadT.L0T (RuntimeLayout.ofPlaceW hpw (Spike.Lib.A64.HelloPh.C0S.immsH Λ0 i0)).Λ) l b)
      ar [] (wcJ0 (mWC lab σC (Spike.Lib.A64.HelloPh.Land.Jr1LH hpw i0 l b)).J σ1) R F := by
  have hpin : (RuntimeLayout.ofPlaceW hpw (Spike.Lib.A64.HelloPh.C0S.immsH Λ0 i0)).pinA.toNat < 2 ^ 32 :=
    (RuntimeLayout.ofPlaceW hpw _).words_small _ (RuntimeLayout.ofPlaceW hpw _).pin_mem
  refine habCtlHA_c0H (fun _ _ h => h) ?_ hctr hcells hu ?_ hlo hhi
  · rw [hmt_HA hpw i0 hl, hslot, Spike.Lib.A64.Rt.pinA_lab0, BitVec.add_zero,
      BitVec.toNat_add, BitVec.toNat_ofNat]
    congr 1; omega
  · show Spike.Lib.A64.HelloPh.C0S.immsH Λ0 i0 newTerm "z" 0 = some 0
    unfold Spike.Lib.A64.HelloPh.C0S.immsH
    split
    · next h => exact absurd h.2.1 (by decide)
    · exact hz

/-- At the root's table `ImmsMe.i0M Λ0` (`iRdM Λ0 = immsH Λ0 (i0M Λ0)`), `hz` is `hz_i0M`: left are `l`'s freshness,
the caller's slot `-80` and the arena facts. -/
example {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
    (hpw : PlaceW pcfg Λ0 o) {l : WeakMem.AllocLabel} {b : Nat} {ms : Spike.Lib.MemSide isaLSE2}
    {lab : String → Int64} {ar : Arena} {σC σ1 : FAS} {R : Region} {F : MachineData → Prop}
    (hl : Spike.Lib.WakeLoadT.L0T (RuntimeLayout.ofPlaceW hpw (Spike.Lib.A64.HelloPh.ImmsMe.iRdM Λ0)).Λ l = none)
    (hslot : σC.slot (-80) =
      Spike.Lib.A64.Flow.Ret0.pinA (RuntimeLayout.ofPlaceW hpw (Spike.Lib.A64.HelloPh.ImmsMe.iRdM Λ0)).lab +
        0#64 + 8#64)
    (hctr : ms.ctr = ar.ctr) (hcells : ms.cells = ar.cells) (hu : ms.units 1 .int = 2) (hlo : R.lo ≤ -304)
    (hhi : 0 ≤ R.hi) :
    HabCtlHA ms lab helloSrc (RuntimeLayout.ofPlaceW hpw (Spike.Lib.A64.HelloPh.ImmsMe.iRdM Λ0)).Λ
      (Spike.Lib.A64ConsumerA.upd
        (Spike.Lib.WakeLoadT.L0T (RuntimeLayout.ofPlaceW hpw (Spike.Lib.A64.HelloPh.ImmsMe.iRdM Λ0)).Λ) l b)
      ar [] (wcJ0 (mWC lab σC (Spike.Lib.A64.HelloPh.Land.Jr1LH hpw (Spike.Lib.A64.HelloPh.ImmsMe.i0M Λ0) l b)).J σ1)
      R F :=
  habCtlHA_jr1L hpw _ hl hslot (hz_i0M Λ0) hctr hcells hu hlo hhi

end Spike.Lib.A64.HelloPh.HabCtlA

/-- info: 'Spike.Lib.A64.HelloPh.HabCtlA.wc_heapAb_segWSHA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.HabCtlA.wc_heapAb_segWSHA

/-- info: 'Spike.Lib.A64.HelloPh.HabCtlA.wc_heapAbStubKHA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.HabCtlA.wc_heapAbStubKHA

/-- info: 'Spike.Lib.A64.HelloPh.HabCtlA.placeVal_slot_keptA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.HabCtlA.placeVal_slot_keptA

/-- info: 'Spike.Lib.A64.HelloPh.HabCtlA.placedSE_c0H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.HabCtlA.placedSE_c0H

/-- info: 'Spike.Lib.A64.HelloPh.HabCtlA.habCtlHA_c0H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.HabCtlA.habCtlHA_c0H

/-- info: 'Spike.Lib.A64.HelloPh.HabCtlA.hz_i0M' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.HabCtlA.hz_i0M

/-- info: 'Spike.Lib.A64.HelloPh.HabCtlA.habCtlHA_jr1L' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.HabCtlA.habCtlHA_jr1L

/-- info: 'Spike.Lib.A64.HelloPh.HabCtlA.hmt_HA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.HabCtlA.hmt_HA
