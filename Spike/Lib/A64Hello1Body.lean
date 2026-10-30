/-
**`hello1.w`'s compiled bodies on AArch64**, inside `W`, in any valid
layout of `hello1Prog` (`Spike/Lib/A64Hello1Code.lean`), from checks decided
once on the program (`decide +kernel`).

- `hello1_wc_body_segW`: `wc_main`'s body, from `.0_entry` (`sp` at the
  frame's base, offset `-96`): the block computing `print`'s arguments, the
  call of `scc_rt_print` (`call_nd_FWK`, `print` in the 48 bytes below the
  frame: the region reaches `-144`), and `.sp4`'s `x0 = 0` and return. Exits:
  the return to the saved return address, and `print`'s abort (to
  `scc_rt_abort` with `x0 = 4`, `sp` at `-144`). The source stutters up to
  the return block, where it may take a local run (`hedge`).
- `hello1_wc_segW`: all of `wc_main`, its prologue then the body, from its
  entry invariant (the body's is `wcJ`).

`print`'s write system call stays a given segment (`hsvc`, of the shape
`seg_printW` asks): a write to the output is no row's (`SysOk`); it is
discharged by the output row once the source extern lands.
-/
import Spike.Lib.A64Hello1Segs
import Spike.Lib.A64Ret0
import Spike.Lib.Rt.A64WcRa

namespace Spike.Lib.A64.Flow.Hello1

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (CallerCells blkW_mono nodeW_mono LimOk)
open Spike.Lib.A64.Rt (WcRa)
open Scc.Cert.Rt.A64 (Lays endOf blockAt label_labelGap labelGap)
open Scc.Cert.Rt.A64.Print (printIn)

set_option linter.unusedSimpArgs false

/-! ## `wc_main`'s body -/

/-- `wc_main`'s `.0_entry` block: `print`'s arguments from the frame's
words, then the call. -/
def wcE : List Directive := parseAArch64("ldr x9, [sp, #8]
ubfm x9, x9, #0, #31
str x9, [sp, #40]
ldr x9, [sp]
ldr x10, [sp, #40]
add x9, x9, x10
str x9, [sp, #48]
ldr x9, [sp, #16]
movz x10, #8
madd x9, x9, x10, xzr
str x9, [sp, #56]
ldr x9, [sp, #24]
ldr x10, [sp, #56]
subs xzr, x9, x10
ldr x11, [sp, #24]
ldr x12, [sp, #56]
csel x9, x11, x12, lo
str x9, [sp, #64]
ldr x0, [sp, #48]
ldr x1, [sp, #64]
bl scc_rt_print")

/-- `wc_main`'s `.sp4` block: `x0 = 0`, the epilogue, `ret`. -/
def wcR4 : List Directive := parseAArch64("movz x0, #0
ldr x29, [sp, #80]
ldr x30, [sp, #88]
add sp, sp, #96
ret")

block_spec wcE (-144) 0 (⟨-96, []⟩ : SO) wcE
block_spec wcR4 (-144) 0 (⟨-96, []⟩ : SO) wcR4

/-- **`wc_main`'s body in `prog`**: the two blocks at their labels, `.sp4`
right after the call. -/
def wcBodyIn (prog : List Directive) : Bool :=
  blockAt prog ".L19_wc_main.0_entry" 0 wcE && blockAt prog ".L19_wc_main.sp4" 0 wcR4 &&
    labelGap prog ".L19_wc_main.0_entry" ".L19_wc_main.sp4" 21

theorem hello1_wcBodyIn : wcBodyIn SccCode.hello1Prog = true := by decide +kernel

/-- The frame's words after the `.0_entry` block from `σ`. -/
def wcSl (σ : AS) : Int → BitVec 64 := (arun (fun _ => 0) wcE ⟨0, ⟨-96, []⟩, σ⟩).σ.slot

theorem wcSl_eq (lab : Label → Int64) (pc : Int64) (σ : AS) :
    (arun lab wcE ⟨pc, ⟨-96, []⟩, σ⟩).σ.slot = wcSl σ := by
  rw [wcSl, wcE_run, wcE_run]

/-- The block keeps the frame record. -/
theorem wcSl_rec (σ : AS) : wcSl σ (-16) = σ.slot (-16) ∧ wcSl σ (-8) = σ.slot (-8) := by
  simp only [wcSl, wcE_run]; exact ⟨by simp [Spike.Lib.upd_apply], by simp [Spike.Lib.upd_apply]⟩

/-- The abstract state at `print`'s entry, after the `.0_entry` block from
`σ` (irreducible: the block's closed form is large). -/
@[irreducible] def wcC (lab : Label → Int64) (σ : AS) : AS :=
  (arun lab wcE ⟨lab ".L19_wc_main.0_entry", ⟨-96, []⟩, σ⟩).σ

theorem wcC_eq (lab : Label → Int64) (σ : AS) :
    wcC lab σ = (arun lab wcE ⟨lab ".L19_wc_main.0_entry", ⟨-96, []⟩, σ⟩).σ := by
  unfold wcC; rfl

/-- The block's call leaves the return address `21` instructions on. -/
theorem wcE_X30 (lab : Label → Int64) (pc : Int64) (σ : AS) :
    (arun lab wcE ⟨pc, ⟨-96, []⟩, σ⟩).σ.regs.X30.toBitVec = (pc + Int64.ofNat (4 * 21)).toBitVec := by
  rw [wcE_run]
  show BitVec.ofInt 64 _ = _
  rw [Ret0.ofInt_bmod]
  simp only [BitVec.ofInt_add, Spike.Lib.int64_ofInt_toInt, Int64.toBitVec_add, BitVec.add_assoc]
  rfl

/-- `print`'s ghost: the source control, the caller's `x29`, the return
address. -/
abbrev PG : Type := Ctl × BitVec 64 × BitVec 64

/-- `wc_main`'s body's internal nodes. -/
inductive WN where
  | e | call | sp4

/-- `wc_main`'s body's exits. -/
inductive WX where
  | ret | abort

/-- **The body's nodes**, from the invariant `J` at `.0_entry`. -/
def wN (lab : Label → Int64) (J : AS → Ctl → Prop) : WN → ND
  | .e => ⟨lab ".L19_wc_main.0_entry", ⟨-96, []⟩, J⟩
  | .call => ⟨lab "scc_rt_print", ⟨-96, []⟩, fun σ c => ∃ σ0, J σ0 c ∧ σ = wcC lab σ0⟩
  | .sp4 => ⟨lab ".L19_wc_main.sp4", ⟨-96, []⟩, fun σ c => ∃ σ0, J σ0 c ∧
      ∀ k, -96 ≤ k → k < 0 → k % 8 = 0 → σ.slot k = wcSl σ0 k⟩

/-- **The body's exits**: the caller's node `x`, and `print`'s abort. -/
def wX (lab : Label → Int64) (J : AS → Ctl → Prop) (x : ND) : WX → ND
  | .ret => x
  | .abort => ⟨lab "scc_rt_abort", ⟨-144, []⟩, fun σ c => σ.regs.X0 = 4 ∧ ∃ σ0, J σ0 c⟩

/-- `print`'s region at the call. -/
abbrev pR (R : Region) : Region := R.callee (-96) (-48) 0

/-- **`wc_main`'s body's states inside `W`**, none moved by `K`: the two
blocks', and `print`'s in its region (for every ghost returning to `.sp4`,
the caller's cells outside it holding values). -/
structure WcBody1W (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (J : AS → Ctl → Prop) : Prop where
  e : BlkW W K exe endPc R F (wN (_root_.Executable.labels exe).label J .e) wcE
  print : ∀ g : PG, g.2.2 = ((_root_.Executable.labels exe).label ".L19_wc_main.sp4").toBitVec →
    PrintD.PrintW g.1 g.2.1 g.2.2 W K exe endPc (pR R) (fun m => F m ∧ CallerCells R (-96) (-48) 0 m)
  sp4 : BlkW W K exe endPc R F (wN (_root_.Executable.labels exe).label J .sp4) wcR4

/-- The body is inside the trivial predicate, with no outside moves. -/
theorem WcBody1W.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {J : AS → Ctl → Prop} : WcBody1W (fun _ _ => True) (fun _ _ => False) exe endPc R F J :=
  ⟨BlkW.triv, fun g _ => PrintD.PrintW.triv g.1 g.2.1 g.2.2, BlkW.triv⟩

/-- `PrintW` under a weaker frame condition holds under a stronger one. -/
theorem printW_mono {W : Frag isaLSE2} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {F F' : MachineData → Prop} {c0 : Ctl} {x29 ra : BitVec 64}
    (h : PrintD.PrintW c0 x29 ra W K exe endPc R F) (hFF : ∀ m, F' m → F m) :
    PrintD.PrintW c0 x29 ra W K exe endPc R F' :=
  ⟨blkW_mono h.e hFF, blkW_mono h.n1 hFF, blkW_mono h.loop hFF, blkW_mono h.n3 hFF, nodeW_mono h.fence hFF,
    blkW_mono h.write hFF,
    blkW_mono h.n5 hFF, blkW_mono h.n6 hFF, blkW_mono h.n7 hFF, blkW_mono h.chk2 hFF, blkW_mono h.n9 hFF,
    blkW_mono h.n10 hFF, blkW_mono h.chk3 hFF, blkW_mono h.n12 hFF, blkW_mono h.adv hFF, blkW_mono h.fail hFF,
    blkW_mono h.done hFF⟩

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wc_main`'s body is one segment inside `W`** in any valid layout of
`hello1Prog`: from `.0_entry` (invariant `J`, `sp` at the frame's base) to
the caller's node `x` (pc the saved return address, `hra`; offsets
`⟨0, []⟩`) or `print`'s abort. At the return, `x`'s invariant holds after a
local run of the source of every state with `x0 = 0`, `x29`/`x30` the saved
record and the frame's words as the block left them (`hedge`). `print`'s
write system call is a given segment for every frame condition the call
hands it, which also keeps the saved return address `x.pc` at `-8` of `R`
(`WcRa`; `hsvc`, discharged by the output row once the source extern
lands). Its states lie in `W`, none moved by `K` (`hW`). -/
theorem hello1_wc_body_segW {W : Frag isaLSE2} {K : State → State → Prop}
    (hp : Lays exe SccCode.hello1Prog) (hend : endPc = endOf exe SccCode.hello1Prog)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi)
    {J : AS → Ctl → Prop} {x : ND} (ho : x.o = ⟨0, []⟩)
    (hW : WcBody1W W K exe endPc R F J) (hra : ∀ σ c, J σ c → x.pc = Int64.ofBitVec (σ.slot (-8)))
    (hsvc : ∀ F' : MachineData → Prop, FStable (pR R) F' →
      (∀ m, F' m → (F m ∧ CallerCells R (-96) (-48) 0 m) ∧ WcRa R x.pc m) →
      ∀ g : PG, g.2.2 = ((_root_.Executable.labels exe).label ".L19_wc_main.sp4").toBitVec →
      SegW W K p lbl ms (At exe endPc (pR R) F' (PrintD.N (_root_.Executable.labels exe).label g.1 g.2.1 g.2.2 .svc))
        (At exe endPc (pR R) F' (PrintD.N (_root_.Executable.labels exe).label g.1 g.2.1 g.2.2 .n5)))
    (hedge : ∀ σ c, J σ c → ∀ σ' : AS, (∀ k, -96 ≤ k → k < 0 → k % 8 = 0 → σ'.slot k = wcSl σ k) →
      σ'.regs.X0.toBitVec = 0#64 → σ'.regs.X29.toBitVec = σ.slot (-16) → σ'.regs.X30.toBitVec = σ.slot (-8) →
      ∃ c', LocalRun p c c' ∧ x.J σ' c') :
    SegW W K p lbl ms (At exe endPc R F (wN (_root_.Executable.labels exe).label J .e))
      (fun s c => ∃ y, At exe endPc R F (wX (_root_.Executable.labels exe).label J x y) s c) := by
  have hin := hello1_wcBodyIn
  simp only [wcBodyIn, Bool.and_eq_true] at hin
  obtain ⟨⟨h0, h4⟩, hgap⟩ := hin
  have e4 := label_labelGap hp hgap
  let lab := (_root_.Executable.labels exe).label
  have e4' : lab ".L19_wc_main.sp4" = lab ".L19_wc_main.0_entry" + Int64.ofNat (4 * 21) := e4
  refine fn_segW (N := wN lab J) (E := wX lab J x) (fun i => ?_) WN.e
  cases i
  case e =>
    refine seg_ndW (by simp [wcE]) wcE_ok hF hR hal hlo hhi (code_of hp hend h0 (ofNat4_zero _)) hW.e
      fun σ c hJ => ⟨c, .refl c, .inl ⟨WN.call, ?_, ?_, σ, hJ, (wcC_eq _ _).symm⟩⟩
    · simp only [wN]; rw [wcE_run]
    · simp only [wN]; rw [wcE_run]; rfl
  case call =>
    have hX30 : ∀ σ0, (wcC lab σ0).regs.X30.toBitVec = (lab ".L19_wc_main.sp4").toBitVec := by
      intro σ0
      rw [wcC_eq, wcE_X30, e4']
    refine call_nd_FWK (KC := False) (lo' := -48) (hi' := 0) (M := fun _ => True)
      (Ne := fun g : PG => PrintD.N lab g.1 g.2.1 g.2.2 .e) (Ex := fun g : PG => Print.E lab g.1 g.2.1 g.2.2)
      hR hal hF (by show R.lo ≤ -96 + -48; omega) (by decide) (by show (-96 : Int) < R.hi; omega) (by decide)
      (by show (-96 : Int) % 16 = 0; decide) (by decide) (by decide) (fun h => h.elim) (fun h => h.elim)
      (fun _ h _ => h)
      (fun R' F' hR' hal' hlo' hhi' hF' _ hFF hR'e hcc g hg hK => by
        subst hR'e
        obtain ⟨σC, c, ⟨σ0, -, hσ⟩, ⟨-, -, h30⟩⟩ := hg
        have hg2 : g.2.2 = (lab ".L19_wc_main.sp4").toBitVec := by
          rw [← h30]; show σC.regs.X30.toBitVec = _; rw [hσ]; exact hX30 σ0
        -- the saved return address: the word at `-8`, off `print`'s region, as at the call
        have hra' : ∀ m, F' m → WcRa R x.pc m := fun m hm => by
          obtain ⟨mC, σC', c', hA, ⟨σ0', hJ0', hσ'⟩, -, hkept⟩ := hK m hm
          have hoff : R.Off (-8) := ⟨by decide, by omega, by omega⟩
          have hn : ¬ (R.callee (wN lab J .call).o.sp (-48) 0).Off (-8 - (wN lab J .call).o.sp) := by
            simp only [Region.Off, Region.callee, wN]; omega
          obtain ⟨j, hj, hv⟩ := hA.slot _ hoff
          refine ⟨j, (hkept _ hoff hn).trans hj, ?_⟩
          rw [hv, hσ', wcC_eq, wcSl_eq, (wcSl_rec σ0').2]
          exact (hra σ0' c' hJ0').symm
        exact (seg_print_ofW hp hend SccCode.hello1_print hF' hR' hal' hlo' hhi'
          (printW_mono (hW.print g hg2) fun m h => ⟨hFF m h, hcc m h⟩)
          (hsvc F' hF' (fun m h => ⟨⟨hFF m h, hcc m h⟩, hra' m h⟩) g hg2)).mono_post
          fun _ _ ⟨y, h⟩ => ⟨y, h, trivial⟩)
      (fun _ => rfl) ?_ ?_
    · rintro σC c -
      exact ⟨(c, σC.regs.X29.toBitVec, σC.regs.X30.toBitVec), rfl, rfl, rfl, rfl⟩
    · rintro g y σC c σx c' σR ⟨σ0, hJ0, hσ⟩ ⟨hc, -, h30⟩ hx hreg - hsl
      have hsl' : ∀ k, -96 ≤ k → k < 0 → k % 8 = 0 → σR.slot k = wcSl σ0 k := fun k h1 h2 h3 => by
        rw [hsl k ⟨h3, by omega, by omega⟩ (by simp only [Region.Off, Region.callee, wN]; omega), hσ, wcC_eq, wcSl_eq]
      cases y
      · obtain ⟨rfl, -, -⟩ := hx
        refine .inl ⟨WN.sp4, ?_, rfl, σ0, hc ▸ hJ0, hsl'⟩
        show lab ".L19_wc_main.sp4" = Int64.ofBitVec g.2.2
        rw [← h30]
        show _ = Int64.ofBitVec σC.regs.X30.toBitVec
        rw [hσ, hX30, int64_ofBitVec_toBitVec]
      · obtain ⟨rfl, h4⟩ := hx
        refine .inr ⟨WX.abort, rfl, rfl, ?_, σ0, hc ▸ hJ0⟩
        show σR.regs.X0 = 4
        rw [hreg]; exact h4
  case sp4 =>
    refine seg_ndW (by simp [wcR4]) wcR4_ok hF hR hal hlo hhi (code_of hp hend h4 (ofNat4_zero _)) hW.sp4
      fun σ c ⟨σ0, hJ0, hsl⟩ => ?_
    obtain ⟨c', hr, hx⟩ := hedge σ0 c hJ0 (arun lab wcR4 ⟨lab ".L19_wc_main.sp4", ⟨-96, []⟩, σ⟩).σ
      (by rw [wcR4_run]; exact hsl) (by rw [wcR4_run]; rfl)
      (by rw [wcR4_run]; show σ.slot (-16) = _; rw [hsl _ (by decide) (by decide) (by decide), (wcSl_rec σ0).1])
      (by rw [wcR4_run]; show σ.slot (-8) = _; rw [hsl _ (by decide) (by decide) (by decide), (wcSl_rec σ0).2])
    refine ⟨c', hr, .inr ⟨WX.ret, ?_, ?_, hx⟩⟩
    · show x.pc = (arun lab wcR4 ⟨lab ".L19_wc_main.sp4", ⟨-96, []⟩, σ⟩).pc
      rw [wcR4_run, hra σ0 c hJ0, hsl _ (by decide) (by decide) (by decide), (wcSl_rec σ0).2]
    · show x.o.le (arun lab wcR4 ⟨lab ".L19_wc_main.sp4", ⟨-96, []⟩, σ⟩).so = true
      rw [wcR4_run, ho]; rfl

end Fn

/-! ## `wc_main` -/

/-- **`wc_main`'s body invariant** from its entry invariant `J0`: the frame
record and the five arguments' words as some entry state left them. -/
def wcJ (J0 : AS → Ctl → Prop) (σ : AS) (c : Ctl) : Prop :=
  ∃ σe, J0 σe c ∧ σ.slot (-16) = σe.regs.X29.toBitVec ∧ σ.slot (-8) = σe.regs.X30.toBitVec ∧
    σ.slot (-96) = σe.regs.X0.toBitVec ∧ σ.slot (-88) = σe.regs.X1.toBitVec ∧
    σ.slot (-80) = σe.regs.X2.toBitVec ∧ σ.slot (-72) = σe.regs.X3.toBitVec ∧ σ.slot (-64) = σe.regs.X4.toBitVec

/-- **`wc_main`'s states inside `W`**, none moved by `K`: its prologue's
(from the entry invariant `J0`) and its body's. -/
structure Wc1W (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (ms : MemSide isaLSE2) (J0 : AS → Ctl → Prop) : Prop where
  pro : ProW W K exe endPc R F ms ((_root_.Executable.labels exe).label "wc_main") 96 8 ".L19_wc_main.stack_grow"
    [(.X0, 0), (.X1, 8), (.X2, 16), (.X3, 24), (.X4, 32)] J0
  body : WcBody1W W K exe endPc R F (wcJ J0)

/-- `wc_main` is inside the trivial predicate, with no outside moves. -/
theorem Wc1W.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {ms : MemSide isaLSE2} {J0 : AS → Ctl → Prop} : Wc1W (fun _ _ => True) (fun _ _ => False) exe endPc R F ms J0 :=
  ⟨ProW.triv, WcBody1W.triv⟩

section WcFn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wc_main` is one segment inside `W`** in any valid layout of
`hello1Prog`: from its entry (invariant `J0`, `sp` at the region's base,
the limit word's facts for its frame of 96, `hlim`) to the caller's node
`x` (pc the return address, `hra`; offsets `⟨0, []⟩`) or `print`'s abort:
its prologue, then `hello1_wc_body_segW` from `wcJ J0` (`hsvc`, `hedge` as
there). Its states lie in `W`, none moved by `K` (`hW`). -/
theorem hello1_wc_segW {W : Frag isaLSE2} {K : State → State → Prop}
    (hp : Lays exe SccCode.hello1Prog) (hend : endPc = endOf exe SccCode.hello1Prog)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi)
    {J0 : AS → Ctl → Prop} {x : ND} (ho : x.o = ⟨0, []⟩)
    (hW : Wc1W W K exe endPc R F ms J0)
    (hlim : ∀ σ c, J0 σ c → LimOk ms F exe endPc (tcbA σ.regs 8) (σ.regs.SP.toBitVec - (96 : Int64).toBitVec))
    (hra : ∀ σ c, J0 σ c → x.pc = Int64.ofBitVec σ.regs.X30.toBitVec)
    (hsvc : ∀ F' : MachineData → Prop, FStable (pR R) F' →
      (∀ m, F' m → (F m ∧ CallerCells R (-96) (-48) 0 m) ∧ WcRa R x.pc m) →
      ∀ g : PG, g.2.2 = ((_root_.Executable.labels exe).label ".L19_wc_main.sp4").toBitVec →
      SegW W K p lbl ms (At exe endPc (pR R) F' (PrintD.N (_root_.Executable.labels exe).label g.1 g.2.1 g.2.2 .svc))
        (At exe endPc (pR R) F' (PrintD.N (_root_.Executable.labels exe).label g.1 g.2.1 g.2.2 .n5)))
    (hedge : ∀ σ c, wcJ J0 σ c → ∀ σ' : AS, (∀ k, -96 ≤ k → k < 0 → k % 8 = 0 → σ'.slot k = wcSl σ k) →
      σ'.regs.X0.toBitVec = 0#64 → σ'.regs.X29.toBitVec = σ.slot (-16) → σ'.regs.X30.toBitVec = σ.slot (-8) →
      ∃ c', LocalRun p c c' ∧ x.J σ' c') :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "wc_main", ⟨0, []⟩, J0⟩)
      (fun s c => ∃ y, At exe endPc R F (wX (_root_.Executable.labels exe).label (wcJ J0) x y) s c) := by
  refine SegW.seq (hello1_wc_prologue_segW hp hend (nb := wN (_root_.Executable.labels exe).label (wcJ J0) .e)
    hF hR hal (by omega) hhi rfl (by show SO.le ⟨-96, []⟩ (oFr 96) = true; decide) hW.pro ?_)
    (hello1_wc_body_segW hp hend hF hR hal hlo hhi ho hW.body ?_ hsvc hedge)
  · intro σ c hJ
    have hl := hlim σ c hJ
    refine ⟨hl.rt, hl.mp, hl.unmapped, fun v hv => ⟨hl.room v hv, fun σ' hr hs => ⟨σ, hJ, ?_⟩⟩⟩
    rw [hs, hr]
    simp [stSlots, frSlot, Spike.Lib.upd_apply, frRegs, ldStep, chkRegs]
  · rintro σ c ⟨σe, hJ, -, h8, -⟩
    rw [h8]; exact hra σe c hJ

end WcFn

end Spike.Lib.A64.Flow.Hello1
