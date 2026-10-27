/-
**A user block's states keep the write abort's phase, from the code
predicate** (AArch64): `hab` of the `W2` block consumers
(`Spike/Lib/LowerA64/W2Body.lean`) for a part of a code block (`SubCd`)
whose label is none of the write abort's (`CdCL`, the code predicate `CdC`
with `L ∉ abLabs`). Every fall-through of the block is a position off the
write abort (`posOff_of_subCdL`, the next instruction's for the last one);
its other targets are assumed so (`htgt`), none for a block of loads,
stores and register operations (`fallBlk`).

- `wcL`, `WcL`, `not_abLabs_of_wcL`, `wcL_local`: a user function's local
  label (a user function context's), none of the write abort's.
- `CdCL`, `CdCL.toCdC`, `SubCd.mono`: the code predicate off the write
  abort's labels at a user function's label, a `CdC`.
- `posOff_of_subCdL`: an instruction of such a part is at a position off
  the write abort.
- `blkW_abSt_subCdL`: the consumers' `hab` from `InstOk`, a part of the
  code off the write abort's labels covered at its node's offsets, with no
  `ret`, the pc right after it off the write abort (`hend`), and every
  branch or call target off the write abort (or the abort's entry at
  `x0 ≠ 4`).
- `fallBlk`, `blkW_abSt_fallL`: the same for a block of fall-throughs only
  (no `htgt`).
-/
import Spike.Lib.LowerA64.UserAb
import Spike.Lib.LowerA64.W2Body

namespace Spike.Lib.LowerA64

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks)
open Spike.Lib.A64Consumer
open Spike.Lib.A64ConsumerA (AbSt)
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Rt (InstOk)
open Scc.Cert.Rt.A64 (blockAt isIns)
open Scc.Cert.Ph1A64 (runPhB)
open Spike.Lib.A64.WriteAb (Ab)
open Spike.Lib.A64.AllocG (abLabs)

/-! ## User functions' labels -/

/-- **A user function's local label** (`FnCtx.local` of a context named
`Names.user f`): `.L<digits>_wc_…`. -/
def wcL (L : Label) : Bool :=
  L.toList.take 2 == ['.', 'L'] && ((L.toList.drop 2).dropWhile Char.isDigit).take 4 == ['_', 'w', 'c', '_']

/-- **A user function's local label** (`wcL`). -/
def WcL (L : Label) : Prop := wcL L = true

instance (L : Label) : Decidable (WcL L) := inferInstanceAs (Decidable (_ = true))

/-- **A user function's local label is none of the write abort's.** -/
theorem not_abLabs_of_wcL {L : Label} (h : WcL L) : L ∉ abLabs := by
  intro hm
  have : abLabs.all (fun l => !wcL l) = true := by decide
  have := List.all_eq_true.mp this _ hm
  rw [h] at this; cases this

/-- **A user function's context's local label is a user function's local
label** (`FnCtx.local` at a context named `Names.user n`). -/
theorem wcL_local (c : Scc.Emit.A64.FnCtx) {n : String} (hn : c.name = Scc.Lower.Names.user n) (sfx : String) :
    WcL (c.local sfx) := by
  have e : (c.local sfx).toList = ['.', 'L'] ++
      (Nat.toDigits 10 c.fi ++ ('_' :: ((Scc.Emit.A64.sanitize c.name).toList ++ '.' :: sfx.toList))) := by
    simp [Scc.Emit.A64.FnCtx.local, Scc.Emit.A64.FnCtx.prefix, String.toList_append, Nat.toString_eq_repr,
      Nat.toList_repr]
    rfl
  have es : (Scc.Emit.A64.sanitize c.name).toList =
      ['w', 'c', '_'] ++ (Scc.Emit.A64.sanitize (Scc.Lower.Names.mangle n)).toList := by
    rw [hn]
    simp only [Scc.Emit.A64.sanitize, Scc.Lower.Names.user, String.toList_map, String.toList_append,
      List.map_append]
    rfl
  unfold WcL wcL
  rw [e, es]
  simp only [List.cons_append, List.nil_append, List.drop_succ_cons, List.drop_zero, List.take_succ_cons,
    List.take_zero]
  rw [List.dropWhile_append_of_pos (fun c hc => Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc)]
  simp

/-! ## The code predicate off the write abort's labels -/

/-- **A piece of a user block's code at `pc` off the write abort's labels**:
the code predicate `CdC` at a label `L` none of `abLabs` and a user
function's local label (`WcL`; the runtime's code, e.g. `scc_rt_print`'s
loop branching into the write abort, is never at `CdCL`). -/
def CdCL (prog : List Directive) (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) (ra : Int64)
    (pc : Int64) (blk : List Directive) : Prop :=
  blk.all isIns = true ∧ ∃ L j, (L ∉ abLabs ∧ WcL L) ∧ lab L + Int64.ofNat (4 * j) = pc ∧
    blockAt prog L j blk = true ∧ runPhB okPc ph lab pc ra blk = true

theorem CdCL.toCdC {prog : List Directive} {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64}
    {ra pc : Int64} {blk : List Directive} (h : CdCL prog okPc ph lab ra pc blk) :
    CdC prog okPc ph lab ra pc blk :=
  let ⟨hi, L, j, _, he, hb, hr⟩ := h
  ⟨hi, L, j, he, hb, hr⟩

theorem SubCd.mono {Cd Cd' : Int64 → List Directive → Prop} (hm : ∀ pc blk, Cd pc blk → Cd' pc blk)
    {pc : Int64} {blk : List Directive} (h : SubCd Cd pc blk) : SubCd Cd' pc blk :=
  let ⟨pc0, pre, suf, hc, he⟩ := h
  ⟨pc0, pre, suf, hm _ _ hc, he⟩

/-- **An instruction of a part of the code off the write abort's labels is
at a position off the write abort.** -/
theorem posOff_of_subCdL {prog : List Directive} {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64}
    {ra pc : Int64} {blk : List Directive} (h : SubCd (CdCL prog okPc ph lab ra) pc blk) {i : Nat}
    (hi : i < blk.length) : PosOff prog lab (pc + Int64.ofNat (4 * i)) := by
  obtain ⟨pc0, pre, suf, ⟨-, L, j, hL, hpc0, hb, -⟩, rfl⟩ := h
  have := posOff_of_blockAt (lab := lab) (blockAt_sub hb) hL.1 hi
  rwa [ofNat4_add, ofNat4_add, hpc0] at this

/-! ## The consumers' `hab` -/

/-- **A part of the code off the write abort's labels keeps the write
abort's phase** (`blkW_abSt_pos`): covered at its node's offsets (`hok`),
with no `ret` (`hnr`), the pc right after it a position off the write
abort (`hend`, e.g. `posOff_of_subCdL` at a longer part), and every target
other than an instruction's fall-through a position off the write abort or,
for a `bl scc_rt_abort`, reached at `x0 ≠ 4` (`htgt`). -/
theorem blkW_abSt_subCdL {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
    {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat}
    (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    {R : Region} {F : MachineData → Prop} {n : ND} {blk : List Directive} {lo hi : Int} {ra : Int64}
    (hcd : SubCd (CdCL prog okPc ph lab ra) n.pc blk) (hok : okBlk lo hi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hnr : noRetBlk blk = true) (hend : PosOff prog lab (n.pc + Int64.ofNat (4 * blk.length)))
    (htgt : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) a, classify blk[k] = some a →
      ∀ t ∈ aiTgts lab (n.pc + Int64.ofNat (4 * k) + Int64.ofNat 4) ra a,
        t ≠ n.pc + Int64.ofNat (4 * k) + Int64.ofNat 4 →
        PosOff prog lab t ∨ (a = .bl "scc_rt_abort" ∧ (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.X0 ≠ 4)) :
    BlkW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n blk := by
  have hcd' := hcd
  obtain ⟨pc0, pre, suf, ⟨-, L, j, -, hpc0, hb, hrun⟩, hpc⟩ := hcd'
  have hph := Scc.Cert.Ph1A64.blkPh_of_runPhB hrun (classify_of_okBlk hok)
  rw [hpc] at hph
  have he : lab L + Int64.ofNat (4 * (j + pre.length)) = n.pc := by
    rw [← hpc, ← hpc0, ofNat4_add]
  have hcode := code_of hI.lays hI.endOk (blockAt_sub hb) (q := n.pc) (by rw [hI.labOk]; exact he)
  refine blkW_abSt_pos hI hpr hab hcode hok hR hal hlo hhi hph hnr ?_
  intro σ c hJ k hk a ha t ht
  by_cases hf : t = n.pc + Int64.ofNat (4 * k) + Int64.ofNat 4
  · refine .inl ?_
    have hf' : t = n.pc + Int64.ofNat (4 * (k + 1)) := by rw [hf, ofNat4_succ]; rfl
    rw [hf']
    rcases Nat.lt_or_ge (k + 1) blk.length with h1 | h1
    · exact posOff_of_subCdL hcd h1
    · rw [show k + 1 = blk.length by omega]
      exact hend
  · exact htgt σ c hJ k hk a ha t ht hf

/-- **An instruction falling through to the next** (a load, a store or a
register operation). -/
def fallI : AI → Bool
  | .ldr .. | .str .. | .reg .. => true
  | _ => false

/-- **A block of fall-throughs**: every instruction covered, a load, a store
or a register operation. -/
def fallBlk (blk : List Directive) : Bool :=
  blk.all fun d => match classify d with
    | some a => fallI a
    | none => false

theorem fallBlk_get {blk : List Directive} (h : fallBlk blk = true) {k : Nat} (hk : k < blk.length) {a : AI}
    (ha : classify blk[k] = some a) : fallI a = true := by
  have := List.all_eq_true.mp h _ (List.getElem_mem hk)
  rw [ha] at this
  exact this

theorem noRetBlk_of_fallBlk {blk : List Directive} (h : fallBlk blk = true) : noRetBlk blk = true := by
  unfold noRetBlk
  refine List.all_eq_true.mpr fun d hd => ?_
  have := List.all_eq_true.mp h d hd
  split
  · next r hr => rw [hr] at this; cases this
  · rfl

/-- **A block of fall-throughs off the write abort's labels keeps the write
abort's phase** (`blkW_abSt_subCdL`, no other target): the pc right after it
a position off the write abort (`hend`). -/
theorem blkW_abSt_fallL {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
    {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat}
    (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    {R : Region} {F : MachineData → Prop} {n : ND} {blk : List Directive} {lo hi : Int} {ra : Int64}
    (hcd : SubCd (CdCL prog okPc ph lab ra) n.pc blk) (hok : okBlk lo hi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hf : fallBlk blk = true) (hend : PosOff prog lab (n.pc + Int64.ofNat (4 * blk.length))) :
    BlkW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n blk := by
  refine blkW_abSt_subCdL hI hpr hab hcd hok hR hal hlo hhi (noRetBlk_of_fallBlk hf) hend ?_
  intro σ c hJ k hk a ha t ht hne
  have := fallBlk_get hf hk ha
  cases a <;> simp only [fallI, Bool.false_eq_true] at this <;>
    simp only [aiTgts, List.mem_singleton] at ht <;> exact absurd ht hne

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.blkW_abSt_subCdL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkW_abSt_subCdL

/-- info: 'Spike.Lib.LowerA64.blkW_abSt_fallL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkW_abSt_fallL

end Spike.Lib.LowerA64
