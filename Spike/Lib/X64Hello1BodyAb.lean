/-
**`wc_main`'s body on x86-64 with `print`'s refusal data**: the body of
`Spike/Lib/X64Hello1BodyA.lean` (same nodes `aN`, exits `aX`, source
predicates `pP`, byte count `wcLen`), with `print`'s call through
`print_callAbW` (`Spike/Lib/X64PrintCallAb.lean`): `print`'s block
obligations asked at `PrintAb`'s nodes (`PrintAbW`, whose refusal branch
carries a `Refusal` of the bytes left).

- `pNAb`, `pExb`, `pNeb`: `print`'s nodes, exits and pinned entry at the
  call state, `PrintAb`'s;
- `WcBodyAbW`, `hello1_wc_bodyAb_segW`: as `WcBodyAW`, `hello1_wc_bodyA_segW`;
- `WcAbW`, `hello1_wcAb_segW`: as `WcAW`, `hello1_wcA_segW`.

The byte count is below `2^63` as there (`hm`, `wcC_rsi_lt`).
-/
import Spike.Lib.X64Hello1BodyA
import Spike.Lib.X64PrintCallAb

namespace Spike.Lib.X64.Flow.Hello1

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Ret0 (CallerCells blkW_mono)
open Scc.Cert.Rt.X64 (Lays endOf blockAtB labelGapB code_field label_labelGapB)

set_option linter.unusedSimpArgs false

section Spec

variable (lab : Label → Int64) (R : Region) (J : AS → Ctl → Prop) (Pr Qr : AS → Nat → Ctl → Prop)

/-- `print`'s nodes for the call state `σC`. -/
abbrev pNAb (σC : AS) : Print.PN → ND :=
  PrintAb.N lab σC.regs.rbp.toBitVec (σC.slot (-96)) (σC.regs.get64 .rdi) (σC.regs.get64 .rsi).toNat
    (pP lab R J Pr σC) (pP lab R J Qr σC)

/-- `print`'s exits for the call state `σC`. -/
abbrev pExb (σC : AS) : Print.PX → ND :=
  PrintAb.E lab σC.regs.rbp.toBitVec (σC.slot (-96)) (σC.regs.get64 .rsi).toNat
    (pP lab R J Pr σC) (pP lab R J Qr σC)

/-- `print`'s entry, pinned to the call state `σC`. -/
def pNeb (σC : AS) : ND :=
  ⟨(pNAb lab R J Pr Qr σC .e).pc, (pNAb lab R J Pr Qr σC .e).o,
    fun σ c => (pNAb lab R J Pr Qr σC .e).J σ c ∧ σ = enter (-104) σC⟩

/-- **`wc_main`'s body's states inside `W`**, none moved by `K`: the
blocks', the multiply's, and `print`'s in its region (for every call state
returning to `.x15`, the caller's cells outside it holding values). -/
structure WcBodyAbW (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (F : MachineData → Prop) : Prop where
  e : BlkW W K exe endPc R F (aN (_root_.Executable.labels exe).label R J Pr .e) wcE1
  mul : NodeW W K exe endPc R F (aN (_root_.Executable.labels exe).label R J Pr .mul)
  e2 : BlkW W K exe endPc R F (aN (_root_.Executable.labels exe).label R J Pr .e2) wcE2
  print : ∀ σC : AS, σC.slot (-96) = ((_root_.Executable.labels exe).label ".Lwc_main.x15").toBitVec →
    PrintAb.PrintAbW σC.regs.rbp.toBitVec (σC.slot (-96)) (σC.regs.get64 .rdi) (σC.regs.get64 .rsi).toNat
      (pP (_root_.Executable.labels exe).label R J Pr σC) (pP (_root_.Executable.labels exe).label R J Qr σC)
      W K exe endPc (pR R) (fun m => F m ∧ CallerCells R (-96 - 8) (-40) 16 m)
  x15 : BlkW W K exe endPc R F
    ⟨(_root_.Executable.labels exe).label ".Lwc_main.x15", oB,
      (aN (_root_.Executable.labels exe).label R J Pr .x15).J⟩ wcR15

/-- The body is inside the trivial predicate, with no outside moves. -/
theorem WcBodyAbW.triv {exe : _root_.Executable} {endPc : Int64} {F : MachineData → Prop} :
    WcBodyAbW R J Pr Qr (fun _ _ => True) (fun _ _ => False) exe endPc F :=
  ⟨BlkW.triv, NodeW.triv, BlkW.triv, fun _ _ => PrintAb.PrintAbW.triv .., BlkW.triv⟩

end Spec

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wc_main`'s body is one segment inside `W`** against a byte-by-byte
source, in any valid layout of `hello1Cells`: from `.entry` (invariant `J`,
`%rsp` at the frame's base, `%rbp` at the saved `%rbp`) to the caller's node
`x` (pc the saved return address, `hra`; offsets at most `⟨8, []⟩`) or
`print`'s abort. The source enters `print` by a local run (`hcall`), moves
inside it only at the write system call (`hsys`), and leaves it by a local
run at the return block (`hedge`). -/
theorem hello1_wc_bodyAb_segW {W : Frag isa} {K : State → State → Prop}
    (hp : Lays exe SccCode.hello1Cells) (hend : endPc = endOf exe SccCode.hello1Cells)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -144) (hhi : 8 ≤ R.hi)
    {J : AS → Ctl → Prop} {Pr Qr : AS → Nat → Ctl → Prop} {x : ND} (ho : SO.le x.o ⟨8, []⟩ = true)
    (hW : WcBodyAbW R J Pr Qr W K exe endPc F)
    (hm : ∀ σ c, J σ c → (σ.slot (-32)).toNat * 8 < 2 ^ 63)
    (hra : ∀ σ c, J σ c → x.pc = Int64.ofBitVec (σ.slot 0))
    (hcall : ∀ σ c, J σ c → ∃ c', LocalRun p c c' ∧ Pr σ 0 c')
    (hsys : ∀ F' : MachineData → Prop, FStable (pR R) F' →
      (∀ m, F' m → F m ∧ CallerCells R (-96 - 8) (-40) 16 m) →
      ∀ σC : AS, σC.slot (-96) = ((_root_.Executable.labels exe).label ".Lwc_main.x15").toBitVec →
      SegW W K p lbl ms (At exe endPc (pR R) F' (pNAb (_root_.Executable.labels exe).label R J Pr Qr σC .sys))
        (At exe endPc (pR R) F' (pNAb (_root_.Executable.labels exe).label R J Pr Qr σC .n5)))
    (hedge : ∀ σ0 c0, J σ0 c0 → σ0.regs.get64 .rbp = R.addr (-8) → ∀ c, Pr σ0 (wcLen σ0) c → ∀ σ' : AS,
      (∀ k, -88 ≤ k → k < 8 → k % 8 = 0 → σ'.slot k = wcSl (_root_.Executable.labels exe).label σ0 k) →
      σ'.regs.rax.toBitVec = 0#64 → σ'.regs.rbp.toBitVec = σ0.slot (-8) →
      σ'.regs.rsp.toBitVec = σ0.regs.rbp.toBitVec + 8#64 + 8#64 →
      ∃ c', LocalRun p c c' ∧ x.J σ' c') :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label ".Lwc_main.entry", oB, J⟩)
      (fun s c => ∃ y, At exe endPc R F (aX (_root_.Executable.labels exe).label J Qr x y) s c) := by
  have hin := hello1_wcBodyIn
  simp only [wcBodyIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨h0, hmu⟩, h2⟩, h15⟩, hgap⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  have e15 : lab ".Lwc_main.x15" = lab ".Lwc_main.entry" + Int64.ofNat 87 := label_labelGapB hp hgap
  refine (fn_segW (N := aN lab R J Pr) (E := aX lab J Qr x) (fun i => ?_) WN.e).mono_pre
    fun _ _ h => At.reg_addr (r := .rbp) (k := -8) rfl h
  cases i
  case e =>
    refine seg_ndW (by simp [wcE1]) wcE1_ok hF hR hlo hhi (code_field hp hend h0 (ofNat_zero' _)) hW.e
      fun σ c hJ => ?_
    obtain ⟨c', hr, hP⟩ := hcall σ c hJ.1
    refine ⟨c', hr, .inl ⟨WN.mul, ?_, ?_, σ, c, hJ, rfl, hP⟩⟩
    · simp only [aN]; rw [wcE1_run]
    · simp only [aN]; rw [wcE1_run]; rfl
  case mul =>
    refine flag_ndW (fi := wcMul) (z := 4) rfl hF (code_field hp hend hmu rfl) hW.mul
      fun σ c ⟨σ0, c0, hJ0, hσ, hP⟩ fl => ⟨c, .refl c, .inl ⟨WN.e2, ?_, ?_, σ0, c0, fl, hJ0, by rw [hσ], hP⟩⟩
    · show lab ".Lwc_main.entry" + 40 = lab ".Lwc_main.entry" + 36 + Int64.ofNat 4
      rw [Int64.add_assoc]; rfl
    · rfl
  case e2 =>
    refine seg_ndW (by simp [wcE2]) wcE2_ok hF hR hlo hhi (code_field hp hend h2 rfl) hW.e2
      fun σ c ⟨σ0, c0, fl, hJ0, hσ, hP⟩ => ⟨c, .refl c, .inl ⟨WN.call, ?_, ?_, σ0, c0, fl, hJ0, ?_, hP⟩⟩
    · simp only [aN]; rw [wcE2_run]
    · simp only [aN]; rw [wcE2_run]; rfl
    · rw [hσ, wcC_eq]; rfl
  case call =>
    refine print_callAbW (nC := aN lab R J Pr .call) (Pc := pP lab R J Pr) (Qc := pP lab R J Qr) hp hend
      SccCode.hello1_print hF hR (by show R.lo ≤ -96 - 8 + -40; omega)
      (by show (-96 : Int) - 8 + 16 ≤ R.hi; omega) (by show ((-96 : Int) - 8) % 8 = 0; decide) rfl
      ?_ ?_ ?_ ?_ ?_ ?_
    · rintro σC c ⟨σ0, c0, fl, hJ0, hσ, hP⟩
      exact ⟨σ0, c0, fl, hJ0, hσ.symm, hP⟩
    · rintro σC c ⟨σ0, c0, fl, hJ0, rfl, -⟩
      exact wcC_rsi_lt lab σ0 fl (hm σ0 c0 hJ0.1)
    · rintro σC c ⟨σ0, c0, fl, hJ0, rfl, -⟩
      exact hW.print _ (wcC_ra lab σ0 fl e15)
    · rintro F' hF' hFF σC c ⟨σ0, c0, fl, hJ0, rfl, -⟩
      exact hsys F' hF' hFF _ (wcC_ra lab σ0 fl e15)
    · rintro σC c σR c' ⟨σ0, c0, fl, hJ0, hσ, -⟩ hbx ⟨σ1, c1, fl1, hJ1, hg1, hP1⟩ hsl
      have hsl' : ∀ k, -88 ≤ k → k < 8 → k % 8 = 0 → σR.slot k = wcSl lab σ0 k := fun k h1 h2 h3 => by
        rw [hsl k ⟨h3, by omega, by omega⟩ (by simp only [Region.Off, Region.callee, aN]; omega), hσ, wcC_slot]
      have hw : wcSl lab σ1 = wcSl lab σ0 := by
        funext k
        rw [← wcC_slot lab σ1 fl1, ← wcC_slot lab σ0 fl, hg1, hσ]
      have hl : (σC.regs.get64 .rsi).toNat = wcLen σ1 := by rw [← hg1, wcC_len]
      refine .inl ⟨WN.x15, ?_, rfl, σ1, c1, hJ1, hl ▸ hP1, ?_, fun k h1 h2 h3 => by rw [hw]; exact hsl' k h1 h2 h3⟩
      · show lab ".Lwc_main.x15" = Int64.ofBitVec (σC.slot (-96))
        rw [hσ, wcC_ra lab σ0 fl e15, int64_ofBitVec_toBitVec]
      · show σR.regs.get64 .rbp = R.addr (-8)
        rw [hbx, hσ]
        show (wcC lab σ0 fl).regs.get64 .rbp = _
        rw [wcC_rbp]; exact hJ0.2
    · rintro σC c σR c' k - h4 ⟨σ1, c1, fl1, hJ1, -, hQ1⟩ -
      exact .inr ⟨WX.abort, rfl, rfl, h4, σ1, c1, k, hJ1.1, hQ1⟩
  case x15 =>
    refine (seg_ndW (n := ⟨lab ".Lwc_main.x15", oB, (aN lab R J Pr .x15).J⟩) (by simp [wcR15]) wcR15_ok hF hR
      hlo hhi (code_field hp hend h15 (ofNat_zero' _)) hW.x15 fun σ c ⟨σ0, c0, hJ0, hP, hb, hsl⟩ => ?_).mono_pre
      fun _ _ h => At.rbp_addr h fun _ _ ⟨_, _, _, _, hb, _⟩ => hb
    have e8 : σ.slot (-8) = σ0.slot (-8) := by rw [hsl _ (by decide) (by decide) (by decide), (wcSl_rec lab σ0).1]
    have e0 : σ.slot 0 = σ0.slot 0 := by rw [hsl _ (by decide) (by decide) (by decide), (wcSl_rec lab σ0).2]
    have hbb : σ.regs.rbp.toBitVec = σ0.regs.rbp.toBitVec := by
      show σ.regs.get64 .rbp = σ0.regs.get64 .rbp; rw [hb, hJ0.2]
    obtain ⟨c', hr, hx⟩ := hedge σ0 c0 hJ0.1 hJ0.2 c hP (arun lab wcR15 ⟨lab ".Lwc_main.x15", oB, σ⟩).σ
      (by rw [wcR15_run]; exact hsl) (by rw [wcR15_run]; simp [Reg64s.set64])
      (by rw [wcR15_run]; simp [Reg64s.set64, e8]) (by rw [wcR15_run]; simp [Reg64s.set64, hbb])
    refine ⟨c', hr, .inr ⟨WX.ret, ?_, ?_, hx⟩⟩
    · show x.pc = (arun lab wcR15 ⟨lab ".Lwc_main.x15", oB, σ⟩).pc
      rw [wcR15_run, hra σ0 c0 hJ0.1, e0]
    · show x.o.le (arun lab wcR15 ⟨lab ".Lwc_main.x15", oB, σ⟩).so = true
      rw [wcR15_run]; exact ho

end Fn

/-! ## `wc_main` -/

/-- **`wc_main`'s states inside `W`** against a byte-by-byte source, none
moved by `K`: its prologue's (from the entry invariant `J0`) and its
body's (`Pr`, `Qr` on the body's entry state). -/
structure WcAbW (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (ms : MemSide isa) (J0 : AS → Ctl → Prop)
    (Pr Qr : AS → Nat → Ctl → Prop) : Prop where
  pro : XProW W K exe endPc R F ms ((_root_.Executable.labels exe).label "wc_main") 80 8 ".Lwc_main.stk" 5 9 3 2 4
    [(.rdi, -8, 4), (.rsi, -16, 4), (.rdx, -24, 4), (.rcx, -32, 4), (.r8, -40, 4)] J0
  body : WcBodyAbW R (wcJ J0) Pr Qr W K exe endPc F

/-- `wc_main` is inside the trivial predicate, with no outside moves. -/
theorem WcAbW.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {ms : MemSide isa} {J0 : AS → Ctl → Prop} {Pr Qr : AS → Nat → Ctl → Prop} :
    WcAbW (fun _ _ => True) (fun _ _ => False) exe endPc R F ms J0 Pr Qr :=
  ⟨XProW.triv, WcBodyAbW.triv ..⟩

section WcFn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wc_main` is one segment inside `W`** against a byte-by-byte source,
in any valid layout of `hello1Cells`: its prologue, then
`hello1_wc_bodyAb_segW` from `wcJ J0` (`hm` on the entry's `%rdx`, the
slice's word count; `hcall`, `hsys`, `hedge` as there). -/
theorem hello1_wcAb_segW {W : Frag isa} {K : State → State → Prop}
    (hp : Lays exe SccCode.hello1Cells) (hend : endPc = endOf exe SccCode.hello1Cells)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -144) (hhi : 8 ≤ R.hi)
    {J0 : AS → Ctl → Prop} {Pr Qr : AS → Nat → Ctl → Prop} {x : ND} (ho : SO.le x.o ⟨8, []⟩ = true)
    (hW : WcAbW W K exe endPc R F ms J0 Pr Qr)
    (hlim : ∀ σ c, J0 σ c → Ret0.LimOk ms F (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec)
      (σ.regs.rsp.toBitVec - 8#64 - (80 : Int64).toBitVec))
    (hm : ∀ σ c, J0 σ c → σ.regs.rdx.toBitVec.toNat * 8 < 2 ^ 63)
    (hra : ∀ σ c, J0 σ c → x.pc = Int64.ofBitVec (σ.slot 0))
    (hcall : ∀ σ c, wcJ J0 σ c → ∃ c', LocalRun p c c' ∧ Pr σ 0 c')
    (hsys : ∀ F' : MachineData → Prop, FStable (pR R) F' →
      (∀ m, F' m → F m ∧ CallerCells R (-96 - 8) (-40) 16 m) →
      ∀ σC : AS, σC.slot (-96) = ((_root_.Executable.labels exe).label ".Lwc_main.x15").toBitVec →
      SegW W K p lbl ms
        (At exe endPc (pR R) F' (pNAb (_root_.Executable.labels exe).label R (wcJ J0) Pr Qr σC .sys))
        (At exe endPc (pR R) F' (pNAb (_root_.Executable.labels exe).label R (wcJ J0) Pr Qr σC .n5)))
    (hedge : ∀ σ0 c0, wcJ J0 σ0 c0 → σ0.regs.get64 .rbp = R.addr (-8) → ∀ c, Pr σ0 (wcLen σ0) c →
      ∀ σ' : AS,
      (∀ k, -88 ≤ k → k < 8 → k % 8 = 0 → σ'.slot k = wcSl (_root_.Executable.labels exe).label σ0 k) →
      σ'.regs.rax.toBitVec = 0#64 → σ'.regs.rbp.toBitVec = σ0.slot (-8) →
      σ'.regs.rsp.toBitVec = σ0.regs.rbp.toBitVec + 8#64 + 8#64 →
      ∃ c', LocalRun p c c' ∧ x.J σ' c') :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "wc_main", ⟨0, []⟩, J0⟩)
      (fun s c => ∃ y, At exe endPc R F (aX (_root_.Executable.labels exe).label (wcJ J0) Qr x y) s c) := by
  refine SegW.seq (hello1_wc_prologue_segW hp hend
    (nb := ⟨(_root_.Executable.labels exe).label ".Lwc_main.entry", oB, wcJ J0⟩) hF hR (by omega) (by omega) rfl
    (by show SO.le oB (oF 80) = true; decide) hW.pro ?_)
    (hello1_wc_bodyAb_segW hp hend hF hR hlo hhi ho hW.body ?_ ?_ hcall hsys hedge)
  · intro σ c hJ
    have hl := hlim σ c hJ
    refine ⟨hl.rt, hl.mp, hl.unmapped, fun v hv => ⟨hl.room v hv, fun σ' hr hs => ⟨σ, hJ, ?_⟩⟩⟩
    rw [hs, hr]
    simp [xStSlots, xS1, upd_apply, xFrRegs, hdRegs, Reg64s.set64, Reg64s.get64]
  · rintro σ c ⟨σe, hJ, -, -, -, -, h32, -, -⟩
    rw [h32]; exact hm σe c hJ
  · rintro σ c ⟨σe, hJ, h0, -⟩
    rw [h0]; exact hra σe c hJ

end WcFn

end Spike.Lib.X64.Flow.Hello1
