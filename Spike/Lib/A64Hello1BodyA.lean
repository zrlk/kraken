/-
**`wc_main`'s body on AArch64 against a byte-by-byte source**: the body of
`Spike/Lib/A64Hello1Body.lean` (same blocks, same call), with `print`'s
call through `seg_printA_ofW` (`Spike/Lib/A64PrintA.lean`) so that the
source moves inside the call by the bytes written.

The caller gives two predicates on the body's entry state `σ0` and the
source control: `Pr σ0 k` (inside `print` with `k` bytes out) and `Qr σ0 k`
(a refused write after `k` bytes justifies the abort). `print`'s ghost is
the abstract state at the call (`σC = wcC lab σ0`, pinned by the callee's
entry node `pNe`); its `P`/`Q` are `Pr`/`Qr` of an entry state that leads
to `σC` (`pP`). The byte count handed to `print` is `wcLen σ0` =
`min(n, 8·m)` (`wcC_x1`), below `2^63` when `8·m` is (`hm`).

- `.e` (the entry invariant `J`) takes a local run of the source to
  `Pr σ0 0` (`hcall`: the source's call of `print`);
- `.sp4` holds `Pr σ0 (wcLen σ0)`; the return takes a local run (`hedge`:
  the source's return from `print`, then the body's tail);
- the abort exit holds `Qr σ0 k` for some `k`.

`hello1_wcA_segW` is all of `wc_main`: its prologue, then this body.

`print`'s write system call stays a given segment (`hsvc`, of the shape
`seg_printAW` asks), for the output row (`Out.emit`) to discharge.
-/
import Spike.Lib.A64Hello1PrintLen
import Spike.Lib.A64PrintA
import Spike.Lib.A64PrintCall

namespace Spike.Lib.A64.Flow.Hello1

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (CallerCells blkW_mono LimOk)
open Scc.Cert.Rt.A64 (Lays endOf label_labelGap)

set_option linter.unusedSimpArgs false

/-- The byte count `print` gets from the body's entry state: `min(n, m·8)`
(`n` at `-72`, `m` at `-80`). -/
def wcLen (σ : AS) : Nat := min (σ.slot (-72)).toNat (σ.slot (-80) * 8#64).toNat

theorem wcC_len (lab : Label → Int64) (σ : AS) : (wcC lab σ).regs.X1.toBitVec.toNat = wcLen σ := wcC_x1 lab σ

section Spec

variable (lab : Label → Int64) (J : AS → Ctl → Prop) (Pr Qr : AS → Nat → Ctl → Prop)

/-- `print`'s source predicate at the call state `σC`: `Pr` of an entry
state leading to `σC`. -/
def pP (σC : AS) (k : Nat) (c : Ctl) : Prop := ∃ σ0 c0, J σ0 c0 ∧ wcC lab σ0 = σC ∧ Pr σ0 k c

/-- `print`'s nodes for the call state `σC`. -/
abbrev pNA (σC : AS) : Print.PN → ND :=
  PrintA.N lab σC.regs.X29.toBitVec σC.regs.X30.toBitVec σC.regs.X0.toBitVec σC.regs.X1.toBitVec.toNat
    (pP lab J Pr σC) (pP lab J Qr σC)

/-- `print`'s exits for the call state `σC`. -/
abbrev pEx (σC : AS) : Print.PX → ND :=
  PrintA.E lab σC.regs.X29.toBitVec σC.regs.X30.toBitVec σC.regs.X1.toBitVec.toNat
    (pP lab J Pr σC) (pP lab J Qr σC)

/-- `print`'s entry, pinned to the call state `σC`. -/
def pNe (σC : AS) : ND :=
  ⟨(pNA lab J Pr Qr σC .e).pc, (pNA lab J Pr Qr σC .e).o,
    fun σ c => (pNA lab J Pr Qr σC .e).J σ c ∧ σ = enter (-96) σC⟩

/-- **The body's nodes**, from the invariant `J` at `.0_entry`. -/
def aN : WN → ND
  | .e => ⟨lab ".L19_wc_main.0_entry", ⟨-96, []⟩, J⟩
  | .call => ⟨lab "scc_rt_print", ⟨-96, []⟩, fun σ c => ∃ σ0 c0, J σ0 c0 ∧ σ = wcC lab σ0 ∧ Pr σ0 0 c⟩
  | .sp4 => ⟨lab ".L19_wc_main.sp4", ⟨-96, []⟩, fun σ c => ∃ σ0 c0, J σ0 c0 ∧ Pr σ0 (wcLen σ0) c ∧
      ∀ k, -96 ≤ k → k < 0 → k % 8 = 0 → σ.slot k = wcSl σ0 k⟩

/-- **The body's exits**: the caller's node `x`, and `print`'s abort. -/
def aX (x : ND) : WX → ND
  | .ret => x
  | .abort => ⟨lab "scc_rt_abort", ⟨-144, []⟩, fun σ c => σ.regs.X0 = 4 ∧ ∃ σ0 c0 k, J σ0 c0 ∧ Qr σ0 k c⟩

/-- **`wc_main`'s body's states inside `W`**, none moved by `K`: the two
blocks', and `print`'s in its region (for every call state returning to
`.sp4`, the caller's cells outside it holding values). -/
structure WcBodyAW (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) : Prop where
  e : BlkW W K exe endPc R F (aN (_root_.Executable.labels exe).label J Pr .e) wcE
  print : ∀ σC : AS, σC.regs.X30.toBitVec = ((_root_.Executable.labels exe).label ".L19_wc_main.sp4").toBitVec →
    PrintA.PrintAW σC.regs.X29.toBitVec σC.regs.X30.toBitVec σC.regs.X0.toBitVec σC.regs.X1.toBitVec.toNat
      (pP (_root_.Executable.labels exe).label J Pr σC) (pP (_root_.Executable.labels exe).label J Qr σC)
      W K exe endPc (pR R) (fun m => F m ∧ CallerCells R (-96) (-48) 0 m)
  sp4 : BlkW W K exe endPc R F (aN (_root_.Executable.labels exe).label J Pr .sp4) wcR4

/-- The body is inside the trivial predicate, with no outside moves. -/
theorem WcBodyAW.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} :
    WcBodyAW J Pr Qr (fun _ _ => True) (fun _ _ => False) exe endPc R F :=
  ⟨BlkW.triv, fun _ _ => PrintA.PrintAW.triv .., BlkW.triv⟩

end Spec

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wc_main`'s body is one segment inside `W`** against a byte-by-byte
source, in any valid layout of `hello1Prog`: from `.0_entry` (invariant
`J`) to the caller's node `x` (pc the saved return address, `hra`; offsets
`⟨0, []⟩`) or `print`'s abort. The source enters `print` by a local run
(`hcall`), moves inside it only at the write system call (`hsvc`), and
leaves it by a local run at the return block (`hedge`). -/
theorem hello1_wc_bodyA_segW {W : Frag isaLSE2} {K : State → State → Prop}
    (hp : Lays exe SccCode.hello1Prog) (hend : endPc = endOf exe SccCode.hello1Prog)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi)
    {J : AS → Ctl → Prop} {Pr Qr : AS → Nat → Ctl → Prop} {x : ND} (ho : x.o = ⟨0, []⟩)
    (hW : WcBodyAW J Pr Qr W K exe endPc R F)
    (hm : ∀ σ c, J σ c → (σ.slot (-80)).toNat * 8 < 2 ^ 63)
    (hra : ∀ σ c, J σ c → x.pc = Int64.ofBitVec (σ.slot (-8)))
    (hcall : ∀ σ c, J σ c → ∃ c', LocalRun p c c' ∧ Pr σ 0 c')
    (hsvc : ∀ F' : MachineData → Prop, FStable (pR R) F' → (∀ m, F' m → F m ∧ CallerCells R (-96) (-48) 0 m) →
      ∀ σC : AS, σC.regs.X30.toBitVec = ((_root_.Executable.labels exe).label ".L19_wc_main.sp4").toBitVec →
      SegW W K p lbl ms (At exe endPc (pR R) F' (pNA (_root_.Executable.labels exe).label J Pr Qr σC .svc))
        (At exe endPc (pR R) F' (pNA (_root_.Executable.labels exe).label J Pr Qr σC .n5)))
    (hedge : ∀ σ0 c0, J σ0 c0 → ∀ c, Pr σ0 (wcLen σ0) c →
      ∀ σ' : AS, (∀ k, -96 ≤ k → k < 0 → k % 8 = 0 → σ'.slot k = wcSl σ0 k) →
      σ'.regs.X0.toBitVec = 0#64 → σ'.regs.X29.toBitVec = σ0.slot (-16) → σ'.regs.X30.toBitVec = σ0.slot (-8) →
      ∃ c', LocalRun p c c' ∧ x.J σ' c') :
    SegW W K p lbl ms (At exe endPc R F (aN (_root_.Executable.labels exe).label J Pr .e))
      (fun s c => ∃ y, At exe endPc R F (aX (_root_.Executable.labels exe).label J Qr x y) s c) := by
  have hin := hello1_wcBodyIn
  simp only [wcBodyIn, Bool.and_eq_true] at hin
  obtain ⟨⟨h0, h4⟩, hgap⟩ := hin
  have e4 := label_labelGap hp hgap
  let lab := (_root_.Executable.labels exe).label
  have e4' : lab ".L19_wc_main.sp4" = lab ".L19_wc_main.0_entry" + Int64.ofNat (4 * 21) := e4
  have hX30 : ∀ σ0, (wcC lab σ0).regs.X30.toBitVec = (lab ".L19_wc_main.sp4").toBitVec := by
    intro σ0
    rw [wcC_eq, wcE_X30, e4']
  refine fn_segW (N := aN lab J Pr) (E := aX lab J Qr x) (fun i => ?_) WN.e
  cases i
  case e =>
    refine seg_ndW (by simp [wcE]) wcE_ok hF hR hal hlo hhi (code_of hp hend h0 (ofNat4_zero _)) hW.e
      fun σ c hJ => ?_
    obtain ⟨c', hr, hP⟩ := hcall σ c hJ
    refine ⟨c', hr, .inl ⟨WN.call, ?_, ?_, σ, c, hJ, (wcC_eq _ _).symm, hP⟩⟩
    · simp only [aN]; rw [wcE_run]
    · simp only [aN]; rw [wcE_run]; rfl
  case call =>
    refine print_callW (nC := aN lab J Pr .call) (Pc := pP lab J Pr) (Qc := pP lab J Qr) hp hend
      SccCode.hello1_print hF hR hal (by show R.lo ≤ -96 + -48; omega) (by show (-96 : Int) < R.hi; omega)
      (by show (-96 : Int) % 16 = 0; decide) rfl ?_ ?_ ?_ ?_ ?_ ?_
    · rintro σC c ⟨σ0, c0, hJ0, hσ, hP⟩
      exact ⟨σ0, c0, hJ0, hσ.symm, hP⟩
    · rintro σC c ⟨σ0, c0, hJ0, rfl, -⟩
      exact wcC_x1_lt lab σ0 (hm σ0 c0 hJ0)
    · rintro σC c ⟨σ0, c0, hJ0, rfl, -⟩
      exact hW.print _ (hX30 σ0)
    · rintro F' hF' hFF σC c ⟨σ0, c0, hJ0, rfl, -⟩
      exact hsvc F' hF' hFF _ (hX30 σ0)
    · rintro σC c σR c' ⟨σ0, c0, hJ0, hσ, -⟩ - - ⟨σ1, c1, hJ1, hg1, hP1⟩ hsl
      have hsl' : ∀ k, -96 ≤ k → k < 0 → k % 8 = 0 → σR.slot k = wcSl σ0 k := fun k h1 h2 h3 => by
        rw [hsl k ⟨h3, by omega, by omega⟩ (by simp only [Region.Off, Region.callee, aN]; omega), hσ, wcC_eq,
          wcSl_eq]
      have hw : wcSl σ1 = wcSl σ0 := by
        funext k
        rw [← wcSl_eq lab (lab ".L19_wc_main.0_entry"), ← wcSl_eq lab (lab ".L19_wc_main.0_entry"),
          ← wcC_eq, ← wcC_eq, hg1, hσ]
      have hl : σC.regs.X1.toBitVec.toNat = wcLen σ1 := by rw [← hg1, wcC_len]
      refine .inl ⟨WN.sp4, ?_, rfl, σ1, c1, hJ1, hl ▸ hP1, fun k h1 h2 h3 => by rw [hw]; exact hsl' k h1 h2 h3⟩
      show lab ".L19_wc_main.sp4" = Int64.ofBitVec σC.regs.X30.toBitVec
      rw [hσ, hX30, int64_ofBitVec_toBitVec]
    · rintro σC c σR c' k - h4 ⟨σ1, c1, hJ1, -, hQ1⟩ -
      exact .inr ⟨WX.abort, rfl, rfl, h4, σ1, c1, k, hJ1, hQ1⟩
  case sp4 =>
    refine seg_ndW (by simp [wcR4]) wcR4_ok hF hR hal hlo hhi (code_of hp hend h4 (ofNat4_zero _)) hW.sp4
      fun σ c ⟨σ0, c0, hJ0, hP, hsl⟩ => ?_
    obtain ⟨c', hr, hx⟩ := hedge σ0 c0 hJ0 c hP (arun lab wcR4 ⟨lab ".L19_wc_main.sp4", ⟨-96, []⟩, σ⟩).σ
      (by rw [wcR4_run]; exact hsl) (by rw [wcR4_run]; rfl)
      (by rw [wcR4_run]; show σ.slot (-16) = _; rw [hsl _ (by decide) (by decide) (by decide), (wcSl_rec σ0).1])
      (by rw [wcR4_run]; show σ.slot (-8) = _; rw [hsl _ (by decide) (by decide) (by decide), (wcSl_rec σ0).2])
    refine ⟨c', hr, .inr ⟨WX.ret, ?_, ?_, hx⟩⟩
    · show x.pc = (arun lab wcR4 ⟨lab ".L19_wc_main.sp4", ⟨-96, []⟩, σ⟩).pc
      rw [wcR4_run, hra σ0 c0 hJ0, hsl _ (by decide) (by decide) (by decide), (wcSl_rec σ0).2]
    · show x.o.le (arun lab wcR4 ⟨lab ".L19_wc_main.sp4", ⟨-96, []⟩, σ⟩).so = true
      rw [wcR4_run, ho]; rfl

end Fn

/-! ## `wc_main` -/

/-- **`wc_main`'s states inside `W`** against a byte-by-byte source, none
moved by `K`: its prologue's (from the entry invariant `J0`) and its
body's (`Pr`, `Qr` on the body's entry state). -/
structure WcAW (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (ms : MemSide isaLSE2) (J0 : AS → Ctl → Prop)
    (Pr Qr : AS → Nat → Ctl → Prop) : Prop where
  pro : ProW W K exe endPc R F ms ((_root_.Executable.labels exe).label "wc_main") 96 8 ".L19_wc_main.stack_grow"
    [(.X0, 0), (.X1, 8), (.X2, 16), (.X3, 24), (.X4, 32)] J0
  body : WcBodyAW (wcJ J0) Pr Qr W K exe endPc R F

/-- `wc_main` is inside the trivial predicate, with no outside moves. -/
theorem WcAW.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {ms : MemSide isaLSE2} {J0 : AS → Ctl → Prop} {Pr Qr : AS → Nat → Ctl → Prop} :
    WcAW (fun _ _ => True) (fun _ _ => False) exe endPc R F ms J0 Pr Qr :=
  ⟨ProW.triv, WcBodyAW.triv ..⟩

section WcFn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wc_main` is one segment inside `W`** against a byte-by-byte source,
in any valid layout of `hello1Prog`: its prologue, then
`hello1_wc_bodyA_segW` from `wcJ J0` (`hm` on the entry's `x2`, the slice's
word count; `hcall`, `hsvc`, `hedge` as there). -/
theorem hello1_wcA_segW {W : Frag isaLSE2} {K : State → State → Prop}
    (hp : Lays exe SccCode.hello1Prog) (hend : endPc = endOf exe SccCode.hello1Prog)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi)
    {J0 : AS → Ctl → Prop} {Pr Qr : AS → Nat → Ctl → Prop} {x : ND} (ho : x.o = ⟨0, []⟩)
    (hW : WcAW W K exe endPc R F ms J0 Pr Qr)
    (hlim : ∀ σ c, J0 σ c → LimOk ms F exe endPc (tcbA σ.regs 8) (σ.regs.SP.toBitVec - (96 : Int64).toBitVec))
    (hm : ∀ σ c, J0 σ c → σ.regs.X2.toBitVec.toNat * 8 < 2 ^ 63)
    (hra : ∀ σ c, J0 σ c → x.pc = Int64.ofBitVec σ.regs.X30.toBitVec)
    (hcall : ∀ σ c, wcJ J0 σ c → ∃ c', LocalRun p c c' ∧ Pr σ 0 c')
    (hsvc : ∀ F' : MachineData → Prop, FStable (pR R) F' → (∀ m, F' m → F m ∧ CallerCells R (-96) (-48) 0 m) →
      ∀ σC : AS, σC.regs.X30.toBitVec = ((_root_.Executable.labels exe).label ".L19_wc_main.sp4").toBitVec →
      SegW W K p lbl ms (At exe endPc (pR R) F' (pNA (_root_.Executable.labels exe).label (wcJ J0) Pr Qr σC .svc))
        (At exe endPc (pR R) F' (pNA (_root_.Executable.labels exe).label (wcJ J0) Pr Qr σC .n5)))
    (hedge : ∀ σ0 c0, wcJ J0 σ0 c0 → ∀ c, Pr σ0 (wcLen σ0) c →
      ∀ σ' : AS, (∀ k, -96 ≤ k → k < 0 → k % 8 = 0 → σ'.slot k = wcSl σ0 k) →
      σ'.regs.X0.toBitVec = 0#64 → σ'.regs.X29.toBitVec = σ0.slot (-16) → σ'.regs.X30.toBitVec = σ0.slot (-8) →
      ∃ c', LocalRun p c c' ∧ x.J σ' c') :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "wc_main", ⟨0, []⟩, J0⟩)
      (fun s c => ∃ y, At exe endPc R F (aX (_root_.Executable.labels exe).label (wcJ J0) Qr x y) s c) := by
  refine SegW.seq (hello1_wc_prologue_segW hp hend
    (nb := aN (_root_.Executable.labels exe).label (wcJ J0) Pr .e)
    hF hR hal (by omega) hhi rfl (by show SO.le ⟨-96, []⟩ (oFr 96) = true; decide) hW.pro ?_)
    (hello1_wc_bodyA_segW hp hend hF hR hal hlo hhi ho hW.body ?_ ?_ hcall hsvc hedge)
  · intro σ c hJ
    have hl := hlim σ c hJ
    refine ⟨hl.rt, hl.mp, hl.unmapped, fun v hv => ⟨hl.room v hv, fun σ' hr hs => ⟨σ, hJ, ?_⟩⟩⟩
    rw [hs, hr]
    simp [stSlots, frSlot, Spike.Lib.upd_apply, frRegs, ldStep, chkRegs]
  · rintro σ c ⟨σe, hJ, -, -, -, -, h80, -⟩
    rw [h80]; exact hm σe c hJ
  · rintro σ c ⟨σe, hJ, -, h8, -⟩
    rw [h8]; exact hra σe c hJ

end WcFn

end Spike.Lib.A64.Flow.Hello1
