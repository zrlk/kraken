/-
**The heap abort's control facts at `wXA`, `c0H` placed from `wc_main`'s spills** (x86-64; the twin of
`Spike/Lib/A64HelloHabCtlA.lean`, same names): at level 1 the allocator's control `c0H` holds rodata's slice word
`loc ⟨l, 0⟩` at a dynamic base, so it is placed only where that base is. `HelloWc.wXA` (the heap abort with
`wc_main`'s spilled argument words at its slots `-16 … -48`) records where: on the abort path (region
`R.callee (-304 - 8) (-24) 16`) those slots are outside the callee's window, kept from the caller's memory `m0`
(`CKept`), there the abstraction `σ`'s (`Abs`), and `σ`'s are the call's entry registers.

- `WcHAbStubHA`, `wc_heapAb_segWSHA`: the heap abort's obligations and its segment with no return, at `wXA`.
- `HabCtlHA`: the control facts at `wXA` with the placement under the path's frame condition.
- `wc_heapAbStubKHAg`: `WcHAbStubHA` under `PhRec.K` from `HabCtlHA` at any owned words `own`, the path's
  placement facts (`hP0`) a premise.
- `placeVal_slot_keptA`: a slot of `wc_main`'s frame at or above `-296` on the abort path is `σ`'s.
- `placedSE_c0H`: `c0H` on a slice at `l` placed at four slots (`z` immediate).
- `habCtlHA_c0H`: `HabCtlHA` below `wc_main`'s entry whose caller's controls are `c0H` on the slice at `l`
  (`SlRegs`) and main's id at the caller's slot `-16` (`hmt`); no placement premise.
- `hmt_HA`: main's id at its TCB at `upd LB l b` (`Box.hmt_H`).
- `habCtlHA_jr1L`: at level 1's `Land.Jr1LH hpw i0 l b`, from `l` fresh, the caller's slot `-16` main's TCB and
  the certificate table's `z` (`hz`); `hz_i0M`: `hz` at the root's `HelloImms.i0M`.

**Unlike AArch64**, the abort node is `wXA`'s x86-64 one: `%rsp` at `-304` with the pushed return address
`.Lscc_rt_alloc.full + 12` in that slot (AArch64: `x30 = .L2_scc_rt_alloc.4_full + 8`), so the dispatcher's
region is `R.callee (-304 - 8) (-24) 16` (AArch64: `R.callee (-304) (-48) 0`), with no alignment premise, and
`R.lo ≤ -336`, `-296 ≤ R.hi` (`seg_jabort2RW`'s). The spills are `wc_main`'s argument registers `%rdi`, `%rsi`,
`%rdx`, `%rcx`, `%r8` at `-16 … -48` (AArch64: `x0`–`x4` at `-144 … -112`): the slice's base at `-16`, `m` and
`n` at `-32`, `-40` (`Hello1.mWC` moves `wc_rodata`'s `%rax`, `%rcx`, `%rsi` there), main's id at `-48`, from the
caller's slot `-16` (AArch64: `-80`). `SegWS.liftS_noret` lives with the AArch64 abort files, so
`wc_heapAb_segWSHA` inlines it (as `X64WakeHAb.wc_heapAb_segWS`). `hmt_HA` is `X64HelloBoxM`'s `Box.hmt_H`
(AArch64 copies it to stay off `A64HelloBoxM`); the root's table is `X64.HelloImms`'s (AArch64: `C0S.immsH`,
`ImmsMe`, `ImmsRd`).
-/
import Spike.Lib.X64HelloHabCtlS
import Spike.Lib.X64HelloWcPreA
import Spike.Lib.X64HelloLand1
import Spike.Lib.X64HelloBoxM
import Spike.Lib.X64HelloImms
import Spike.Lib.X64AbortHeapRWCode
import Spike.Lib.X64WakeHAbStubK

namespace Spike.Lib.X64.HelloPh.HabCtlA

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (codeLabel pcOf abi)
open SccCode (helloCells)
open Spike.Lib (Arena FragS Frag Region HeapAbortOblA SegWS Ctl PlaceWX)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64ConsumerS (PlacedSE)
open Spike.Lib.X64 (ND At FStable CKept Abs)
open Spike.Lib.X64.WakeWf (DtW W0 RunWf)
open Spike.Lib.X64.Flow.HelloWc (wXA)
open Spike.Lib.X64.Flow.Hello1 (mWC)
open Spike.Lib.X64.Flow.HelloM (wcJ0)
open Spike.Lib.X64.Flow.HelloJr1 (SlRegs)
open Spike.Lib.X64.HelloPh.StartWf (pfxM)
open Spike.Lib.X64.HelloPh (lo)
open Spike.Lib.X64.HelloPh.HAbStub (hpathW_hXH abort_offH)
open Spike.Lib.X64HelloMainPreSrc (c0H c0H_term boxTermH newTerm)
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.X64WakeSrcDefs (mainTidLbl)
open Spike.Lib.X64WakeLoadT (L0T)
open Spike.Lib.X64.WakeSrcCtl (placedSE_of_tbl rep_at)

set_option linter.unusedSimpArgs false

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.X64.AS

/-! ## The heap abort at `wXA` -/

section Tail

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **The heap abort's obligations at `wXA`** (`X64WakeHAb.WcHAbStub`'s shape): the heap abort path's below
`-304` for every caller's state and source control of `wXA`, the return address `wXA`'s pushed word. -/
def WcHAbStubHA (W : FragS isa) (K : State → State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (ms : List TermRun.Frame → MemSide isa) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (fs : List TermRun.Frame) (J1 : FAS → Ctl → Prop) : Prop :=
  ∀ m0 σC c0, (wXA (ms fs) (_root_.Executable.labels exe).label J1).J σC c0 →
    Abort.Disp.StubHRW (fun s c => W s c fs) K p lbl (ms fs) exe endPc (R.callee (-304 - 8) (-24) 16)
      (fun m => F m ∧ CKept R (-304 - 8) (-24) 16 m0 m ∧ Abs R ⟨-304, []⟩ m0 σC) c0
      ((_root_.Executable.labels exe).label ".Lscc_rt_alloc.full" + 12).toBitVec

/-- **The heap abort at `wXA` does not return** (`seg_jabort2RW` at `-304`). -/
theorem wc_heapAb_segWSHA {W : FragS isa} {K : State → State → Prop} {fs : List TermRun.Frame}
    {J1 : FAS → Ctl → Prop}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -336) (hhi : -296 ≤ R.hi)
    (hK : (ms fs).K = some Scc.Sem.X64.abi) (hstub : WcHAbStubHA W K p lbl ms exe endPc R F fs J1)
    (Q : FragS isa) :
    SegWS W K p lbl ms ((At exe endPc R F (wXA (ms fs) (_root_.Executable.labels exe).label J1)).at fs) Q := by
  have h := Abort.Disp.seg_jabort2RW (p := p) (lbl := lbl) (Q := fun _ _ => False) (W := fun s c => W s c fs)
    (K := K) (nC := wXA (ms fs) (_root_.Executable.labels exe).label J1) rfl
    (fun σ c h => h.1) (fun σ c h => h.2.1) hF hR (by show R.lo ≤ -304 - 32; omega)
    (by show (-304 : Int) + 8 ≤ R.hi; omega) (by show (-304 : Int) % 8 = 0; decide) hK hstub
  exact (SegWS.liftS fs h fun _ _ h => h).mono_post fun _ _ _ h => h.1.elim

end Tail

/-- **The control facts at `wXA` with the placement on the path**: `c0` placed at the states whose memory meets
`F` and keeps the caller's region outside the callee's window from `m0`, abstracted by `wXA`'s `σ`. -/
def HabCtlHA (ms : MemSide isa) (lab : String → Int64) (p : Prog) (Λ : Scc.Sem.Layout) (L0 : Lbl)
    (ar : Arena) (fs : List TermRun.Frame) (J1 : FAS → Ctl → Prop) (R : Region)
    (F : MachineData → Prop) : Prop :=
  ∀ σ c0, (wXA ms lab J1).J σ c0 →
    ((fs = [] → ∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 fs) ∧
      (∀ m0 (s : State), F s.st.1 → CKept R (-304 - 8) (-24) 16 m0 s.st.1 →
        Abs R ⟨-304, []⟩ m0 σ → PlacedSE Λ L0 s c0 fs) ∧
      HeapAbortOblA ar.cells ar.ctr c0

section Inst

variable {L : RuntimeLayout}
variable (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo)
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
include hp hlo hlab

/-- **`WcHAbStubHA` from `HabCtlHA` at any owned words `own`**: the path inside `W0` at `own` with the placement
at the path's frame condition (`hP0`, for every stable frame condition and control the placement and source facts
admit) and in `scc_rt_abort`'s code, whose pcs are off the take site. -/
theorem wc_heapAbStubKHAg {own : Spike.Lib.X64Consumer.Own} {R : Region} {F : MachineData → Prop} {ar : Arena}
    {p : Prog} {Cl : State → Prop} {Ctx : FragS isa} {L0 : Lbl} {ls0 : Lsize} {frM : TermRun.Frame}
    {X0 : State → Prop} {fs : List TermRun.Frame} {lbl : WeakMem.AllocLabel → Option Nat}
    {ms : List TermRun.Frame → MemSide isa} {J1 : FAS → Ctl → Prop} {rS : Scc.Sem.Range}
    (hF : FStable R F) (hR : R.OK) (hlo' : R.lo ≤ -336) (hhi : -296 ≤ R.hi)
    (hK : (ms fs).K = some abi)
    (hctl : HabCtlHA (ms fs) L.lab p L.Λ L0 ar fs J1 R F)
    (hab : ∀ s : State, s.st.2 = L.lab "scc_rt_abort_heap_exit" → (ms fs).abortAt s)
    (hP0 : ∀ (F' : MachineData → Prop) (c0 : Ctl), FStable (R.callee (-304 - 8) (-24) 16) F' →
      ((fs = [] → ∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 fs) → (∀ s : State, F' s.st.1 → PlacedSE L.Λ L0 s c0 fs) →
      HeapAbortOblA ar.cells ar.ctr c0 →
      Abort.Disp.HPathW (fun s c => W0 L.Λ (Spike.Lib.X64.PhRec.μ L) own ar p DtW (Spike.Lib.X64.WriteAb.Ab L.lab)
        Cl (Spike.Lib.X64.Hello.ThreadsAb.AcH L.lab pfxM) Ctx L0 ls0 frM X0 s c fs) (fun _ _ => False) L.exe
        L.endPc (R.callee (-304 - 8) (-24) 16) F' c0 (L.lab ".Lscc_rt_alloc.full" + 12).toBitVec) :
    WcHAbStubHA (W0 L.Λ (Spike.Lib.X64.PhRec.μ L) own ar p DtW (Spike.Lib.X64.WriteAb.Ab L.lab) Cl
      (Spike.Lib.X64.Hello.ThreadsAb.AcH L.lab pfxM) Ctx L0 ls0 frM X0) (Spike.Lib.X64.PhRec.K L rS) p lbl ms L.exe
      L.endPc R F fs J1 := by
  intro m0 σC c0 hJ
  obtain ⟨hc0, hpl, hobl⟩ := hctl σC c0 hJ
  have hR' : (R.callee (-304 - 8) (-24) 16).OK :=
    Region.callee_ok hR (by omega) (by decide) (by omega) (by omega)
  have hF' : FStable (R.callee (-304 - 8) (-24) 16) (fun m => F m ∧
      CKept R (-304 - 8) (-24) 16 m0 m ∧ Abs R ⟨-304, []⟩ m0 σC) :=
    Spike.Lib.X64.fstable_enter hR hF (by omega) (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide)
  have h0 := hP0 (fun m => F m ∧ CKept R (-304 - 8) (-24) 16 m0 m ∧ Abs R ⟨-304, []⟩ m0 σC) c0 hF' hc0
    (fun s h => hpl m0 s h.1 h.2.1 h.2.2) hobl
  have hX := hpathW_hXH (F := fun m => F m ∧ CKept R (-304 - 8) (-24) 16 m0 m ∧
      Abs R ⟨-304, []⟩ m0 σC) (c0 := c0)
    (ra := (L.lab ".Lscc_rt_alloc.full" + 12).toBitVec) hp hlo hlab hR' (by simp [Region.callee])
    (by simp [Region.callee])
  have hpath := Spike.Lib.X64.WakePh.HPathW.map (Spike.Lib.X64.WakePh.HAbStubK.hpathW_K
    (K := Spike.Lib.X64.PhRec.K L rS)
    (Abort.Disp.HPathW.and h0 hX fun _ _ h₁ h₂ => And.intro h₁ h₂)
    fun s _ h s' hk => (abort_offH hlab s h.2).2 (congrArg (fun x : Int64 => x.toBitVec.toNat) hk.1))
    fun _ _ h => h.1
  exact Spike.Lib.X64.StubW.stubHRW_of_code L.lays rfl (by rw [hp]; exact SccCode.hello_abort) hK hF' hpath
    fun s _ ⟨_, _, _, hpc, _⟩ => hab s hpc

end Inst

/-! ## `c0H` placed from the spills -/

/-- **A slot of `wc_main`'s frame on the abort path**: at or above `-296` it is outside the callee's window, so
as in the caller's memory `m0` (`CKept`), there `σ`'s (`Abs`). -/
theorem placeVal_slot_keptA {R : Region} {m0 : MachineData} {σ : FAS} {s : State}
    (hA : Abs R ⟨-304, []⟩ m0 σ) (hK : CKept R (-304 - 8) (-24) 16 m0 s.st.1) {k : Int} (hk : R.Off k)
    (hk' : -296 ≤ k) :
    Scc.Sem.placeVal (Scc.Sem.X64.machine (Scc.Sem.X64.kernel 1)) s (.slot (R.addr k).toNat) =
      some (σ.slot k).toNat := by
  obtain ⟨j, hj, hv⟩ := hA.slot k hk
  have hc : ¬ (R.callee (-304 - 8) (-24) 16).Off (k - (-304 - 8)) := fun ⟨_, _, h3⟩ => by
    simp only [Region.callee] at h3; omega
  show (Scc.Sem.X64.privLoad s (BitVec.ofNat 64 (R.addr k).toNat)).map (·.toNat) = _
  simp [Scc.Sem.X64.privLoad, hK k hk hc, hj, hv]

/-- **`c0H` on the slice at `l` placed at four slots**: the base at `a0` (offset immediate `0`), `m`, `n` at `a2`,
`a3`, main's id at `am`; `z` the layout's immediate `0` at `newTerm` (`hiz`). -/
theorem placedSE_c0H {Λ : Scc.Sem.Layout} {lbl : Lbl} {s : State} {l : WeakMem.AllocLabel} (a0 a2 a3 am : Nat)
    (hiz : Λ.imms newTerm "z" 0 = some 0)
    (h0 : ∃ v, Scc.Sem.placeVal (Scc.Sem.X64.machine (Scc.Sem.X64.kernel 1)) s (.slot a0) = some v ∧
      lbl l = some v)
    (h2 : Scc.Sem.placeVal (Scc.Sem.X64.machine (Scc.Sem.X64.kernel 1)) s (.slot a2) = some 2)
    (h3 : Scc.Sem.placeVal (Scc.Sem.X64.machine (Scc.Sem.X64.kernel 1)) s (.slot a3) = some 13)
    (hm : ∃ v, Scc.Sem.placeVal (Scc.Sem.X64.machine (Scc.Sem.X64.kernel 1)) s (.slot am) = some v ∧
      lbl (mainTidLbl 2) = some v) :
    PlacedSE Λ lbl s (c0H (TermRun.cst (.loc ⟨l, 0⟩ 0)) (TermRun.cst (.num 2)) (TermRun.cst (.num 13))
      Spike.Lib.X64.HelloPh.Land.mwH) [] := by
  refine placedSE_of_tbl [("z", [.imm 0]), ("sl", [.loc (.slot a0) (.imm 0), .one (.slot a2), .one (.slot a3)]),
    ("me", [.one (.slot am)])] ?_ ?_ ?_
  · intro x hx ty ws hl
    rw [show (c0H (TermRun.cst (.loc ⟨l, 0⟩ 0)) (TermRun.cst (.num 2)) (TermRun.cst (.num 13))
      Spike.Lib.X64.HelloPh.Land.mwH).term = newTerm from rfl,
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

/-- **`HabCtlHA` below `c0H` on a slice at `l`** (no placement premise): below `wc_main`'s entry invariant whose
caller's controls are `c0H` on the slice at `l` (`hJr`, `SlRegs` at `L0`) with main's id at the caller's slot
`-16` (`hmt`), the control is placed at `wc_main`'s spills `-16`, `-32`, `-40`, `-48`, given the layout's `z`
(`hiz`) and the arena facts. -/
theorem habCtlHA_c0H {ms : MemSide isa} {lab : String → Int64} {Λ : Scc.Sem.Layout} {L0 : Lbl}
    {ar : Arena} {σC σ1 : FAS} {Jr : FAS → Ctl → Prop} {l : WeakMem.AllocLabel} {R : Region}
    {F : MachineData → Prop}
    (hJr : ∀ σ c, Jr σ c → c = c0H (TermRun.cst (.loc ⟨l, 0⟩ 0)) (TermRun.cst (.num 2)) (TermRun.cst (.num 13))
      Spike.Lib.X64.HelloPh.Land.mwH ∧ SlRegs L0 l σ)
    (hmt : L0 (mainTidLbl 2) = some (σC.slot (-16)).toNat) (hctr : ms.ctr = ar.ctr)
    (hcells : ms.cells = ar.cells) (hu : ms.units 1 .int = 2) (hiz : Λ.imms newTerm "z" 0 = some 0)
    (hlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi) :
    HabCtlHA ms lab helloSrc Λ L0 ar [] (wcJ0 (mWC lab σC Jr).J σ1) R F := by
  rintro σ c0 ⟨-, -, q, hfull, σe, ⟨rfl, σx, hJ, e0, -, e2, e3, e4, -⟩, s0, -, s2, s3, s4⟩
  obtain ⟨hq, hx0, -, hx2, hx3⟩ := hJr σx _ hJ
  have hctl := Spike.Lib.X64.WakeSrcCtl.new_ctl (p := helloSrc) (c0H_term (TermRun.cst (.loc ⟨l, 0⟩ 0))
    (TermRun.cst (.num 2)) (TermRun.cst (.num 13)) Spike.Lib.X64.HelloPh.Land.mwH)
  obtain ⟨T, ht⟩ := q.2.term; rw [hq, c0H_term] at ht
  obtain ⟨-, ha, -⟩ := Expr.let_.inj ht
  have hev := q.2.ev; rw [hq, ← (Op.new.inj ha).1] at hev
  have hz : TermRun.evalAt (c0H (TermRun.cst (.loc ⟨l, 0⟩ 0)) (TermRun.cst (.num 2)) (TermRun.cst (.num 13))
      Spike.Lib.X64.HelloPh.Land.mwH).env (.var "z") = some (.int, [TermRun.cst (.num 0)]) := rfl
  have hτ : q.1.τ = .int := by rw [hz] at hev; exact (Prod.mk.inj (Option.some.inj hev)).1.symm
  rcases hfull with ⟨-, hn⟩ | ⟨o, rfl, -, hlt⟩
  · rw [q.2.one] at hn; exact absurd hn (by decide)
  rw [q.2.one, hτ, hu] at hlt; rw [hq]
  have hoff : ∀ k : Int, k % 8 = 0 → -304 ≤ k → k + 8 ≤ 0 → R.Off k := fun k h1 h2 h3 => ⟨h1, by omega, by omega⟩
  refine ⟨⟨fun _ => hctl.1, Spike.Lib.X64.WakePh.WcWf.RunWf.hold hctl.2⟩, fun m0 s _ hK hA => ?_, fun old h => ?_⟩
  · have pv := fun k hk hk' => placeVal_slot_keptA (s := s) hA hK (k := k) hk hk'
    refine Spike.Lib.X64.WakePh.WcWf.PlacedSE.hold.2 (placedSE_c0H (R.addr (-16)).toNat
      (R.addr (-32)).toNat (R.addr (-40)).toNat (R.addr (-48)).toNat hiz ?_ ?_ ?_ ?_)
    · exact ⟨_, pv (-16) (hoff _ (by decide) (by decide) (by decide)) (by decide), by
      rw [s0]; show _ = some σ1.regs.rdi.toBitVec.toNat; rw [e0]; exact hx0⟩
    · rw [pv (-32) (hoff _ (by decide) (by decide) (by decide)) (by decide), s2]
      show some σ1.regs.rdx.toBitVec.toNat = _; rw [e2, hx2]
    · rw [pv (-40) (hoff _ (by decide) (by decide) (by decide)) (by decide), s3]
      show some σ1.regs.rcx.toBitVec.toNat = _; rw [e3, hx3]
    · exact ⟨_, pv (-48) (hoff _ (by decide) (by decide) (by decide)) (by decide), by
      rw [s4]; show _ = some σ1.regs.r8.toBitVec.toNat; rw [e4]; exact hmt⟩
  · obtain ⟨hle, hw⟩ := h (.inr ⟨"o", .var "z", boxTermH, _, rfl⟩)
    have he := hw _ (by rw [← hctr]; rfl)
    have ho : o.toNat = old := by simpa [TermRun.cst, Promises.TVal.mk0] using he
    exact .inr ⟨"o", .var "z", _, .int, TermRun.cst (.num 0), ⟨_, rfl⟩, rfl, rfl, hle, by rw [← hcells]; omega⟩

section Root

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The root's layout at the certificate's table `i0`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw (Spike.Lib.X64.HelloImms.immsH Λ0 i0)

/-- **main's id at its TCB** at `upd LB l b`, `l` fresh at `LB` (`Box.hmt_H`). -/
theorem hmt_HA {l : WeakMem.AllocLabel} {b : Nat} (hl : L0T (Ly).Λ l = none) :
    Spike.Lib.X64ConsumerA.upd (L0T (Ly).Λ) l b (mainTidLbl 2) = some ((Ly).pinA.toNat + 8) :=
  Spike.Lib.X64.HelloPh.Box.hmt_H hpw i0 hl

/-- **The certificate table's `z` at `newTerm`** through the root's `HelloImms.i0M` (`helloImm_t1`'s entry). -/
theorem hz_i0M (Λ0 : Scc.Sem.Layout) : Spike.Lib.X64.HelloImms.i0M Λ0 newTerm "z" 0 = some 0 := by
  rw [Spike.Lib.X64.HelloImms.i0M_i0Rd fun h => absurd h.2.1 (by decide)]
  exact Spike.Lib.X64.HelloImms.i0Rd_helloImms (by
    have hne : SccCode.helloImm_t1 ≠ SccCode.helloImm_t2 := fun h => absurd (Expr.let_.inj h).1 (by decide)
    rw [show newTerm = SccCode.helloImm_t1 from rfl]; simp [SccCode.helloImms, hne])

/-- **`HabCtlHA` at level 1**: below `Land.Jr1LH hpw i0 l b` at the level's labels `upd LB l b` (`l` fresh at
`LB`, `hl`), the caller's slot `-16` main's TCB (`hslot`, `Land.GcM1H`'s), the certificate table's `z` (`hz`; at
the root `hz_i0M`) and the arena facts. -/
theorem habCtlHA_jr1L {l : WeakMem.AllocLabel} {b : Nat}
    {ms : MemSide isa} {lab : String → Int64} {ar : Arena} {σC σ1 : FAS} {R : Region}
    {F : MachineData → Prop}
    (hl : L0T (Ly).Λ l = none)
    (hslot : σC.slot (-16) = Spike.Lib.X64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64)
    (hz : i0 newTerm "z" 0 = some 0) (hctr : ms.ctr = ar.ctr) (hcells : ms.cells = ar.cells)
    (hu : ms.units 1 .int = 2) (hlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi) :
    HabCtlHA ms lab helloSrc (Ly).Λ (Spike.Lib.X64ConsumerA.upd (L0T (Ly).Λ) l b) ar []
      (wcJ0 (mWC lab σC (Spike.Lib.X64.HelloPh.Land.Jr1LH hpw i0 l b)).J σ1) R F := by
  refine habCtlHA_c0H (fun _ _ h => h.1) ?_ hctr hcells hu ?_ hlo hhi
  · rw [hmt_HA hpw i0 hl, hslot, Spike.Lib.X64.HelloPh.Box.tv_toNat hpw i0]
  · show Spike.Lib.X64.HelloImms.immsH Λ0 i0 newTerm "z" 0 = some 0
    unfold Spike.Lib.X64.HelloImms.immsH
    split
    · next h => exact absurd h.2.1 (by decide)
    · exact hz

end Root

/-- At the root's table `HelloImms.i0M Λ0` (`iRdM Λ0 = immsH Λ0 (i0M Λ0)`), `hz` is `hz_i0M`: left are `l`'s
freshness, the caller's slot `-16` and the arena facts. -/
example {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
    (hpw : PlaceWX pcfg Λ0 o) {l : WeakMem.AllocLabel} {b : Nat} {ms : MemSide isa}
    {lab : String → Int64} {ar : Arena} {σC σ1 : FAS} {R : Region} {F : MachineData → Prop}
    (hl : L0T (RuntimeLayout.ofPlaceWX hpw (Spike.Lib.X64.HelloImms.iRdM Λ0)).Λ l = none)
    (hslot : σC.slot (-16) =
      Spike.Lib.X64.Flow.Ret0.pinA (RuntimeLayout.ofPlaceWX hpw (Spike.Lib.X64.HelloImms.iRdM Λ0)).lab +
        0#64 + 8#64)
    (hctr : ms.ctr = ar.ctr) (hcells : ms.cells = ar.cells) (hu : ms.units 1 .int = 2) (hlo : R.lo ≤ -304)
    (hhi : 0 ≤ R.hi) :
    HabCtlHA ms lab helloSrc (RuntimeLayout.ofPlaceWX hpw (Spike.Lib.X64.HelloImms.iRdM Λ0)).Λ
      (Spike.Lib.X64ConsumerA.upd (L0T (RuntimeLayout.ofPlaceWX hpw (Spike.Lib.X64.HelloImms.iRdM Λ0)).Λ) l b)
      ar [] (wcJ0 (mWC lab σC
        (Spike.Lib.X64.HelloPh.Land.Jr1LH hpw (Spike.Lib.X64.HelloImms.i0M Λ0) l b)).J σ1) R F :=
  habCtlHA_jr1L hpw _ hl hslot (hz_i0M Λ0) hctr hcells hu hlo hhi

end Spike.Lib.X64.HelloPh.HabCtlA

/-- info: 'Spike.Lib.X64.HelloPh.HabCtlA.wc_heapAb_segWSHA'
  depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Spike.Lib.X64.HelloPh.HabCtlA.wc_heapAb_segWSHA

/-- info: 'Spike.Lib.X64.HelloPh.HabCtlA.wc_heapAbStubKHAg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.HabCtlA.wc_heapAbStubKHAg

/-- info: 'Spike.Lib.X64.HelloPh.HabCtlA.placeVal_slot_keptA'
  depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Spike.Lib.X64.HelloPh.HabCtlA.placeVal_slot_keptA

/-- info: 'Spike.Lib.X64.HelloPh.HabCtlA.placedSE_c0H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.HabCtlA.placedSE_c0H

/-- info: 'Spike.Lib.X64.HelloPh.HabCtlA.habCtlHA_c0H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.HabCtlA.habCtlHA_c0H

/-- info: 'Spike.Lib.X64.HelloPh.HabCtlA.hmt_HA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.HabCtlA.hmt_HA

/-- info: 'Spike.Lib.X64.HelloPh.HabCtlA.hz_i0M' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.HabCtlA.hz_i0M

/-- info: 'Spike.Lib.X64.HelloPh.HabCtlA.habCtlHA_jr1L' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.HabCtlA.habCtlHA_jr1L
