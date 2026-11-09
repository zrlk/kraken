/-
**A user block's states keep the write abort's phase, from the code
predicate** (x86-64): `hab` of the `W2` block consumers
(`Spike/Lib/LowerX64/W2Body.lean`) for a part of a code block (`SubCd`)
whose label is none of the write abort's (`CdCL`, the code predicate `CdC`
with `L ∉ abLabs`). Every fall-through of the block is a position off the
write abort (`posOff_of_subCdL`, the next cell's for the last one); its
other targets are assumed so (`htgt`), none for a block of loads, stores,
pushes, pops and register operations (`fallBlk`).

- `WcL`, `CdCL`, `CdCL.toCdC`, `SubCd.mono`: the code predicate off the
  write abort's labels in a user function's run (beginning `.Lwc_`), a `CdC`.
- `posOff_of_subCdL`: a cell of such a part is at a position off the write
  abort.
- `blkW_abSt_subCdL`: the consumers' `hab` from `InstOk`, a part of the
  code off the write abort's labels covered at its node's offsets, with no
  `ret`, the pc right after it off the write abort (`hend`), and every
  branch or call target off the write abort (or the abort's entry at
  `%rdi ≠ 4`).
- `fallBlk`, `blkW_abSt_fallL`: the same for a block of fall-throughs only
  (no `htgt`).

Where x86-64 differs from AArch64: positions are byte offsets (`cellOff`).
-/
import Spike.Lib.LowerX64.UserAb
import Spike.Lib.LowerX64.W2Body

namespace Spike.Lib.LowerX64

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks)
open Spike.Lib.X64Consumer
open Spike.Lib.X64ConsumerA (AbSt)
open Spike.Lib.X64
open Spike.Lib.X64.Rt (InstOk)
open Scc.Cert.Rt.X64 (blockAt)
open Scc.Cert.Ph1X64 (runPhB)
open Spike.Lib.X64.WriteAb (Ab)
open Spike.Lib.X64.AllocG (abLabs)

/-! ## The code predicate off the write abort's labels -/

/-- **A label of a user function's runs**: it begins `.Lwc_` (a user
function's block label `labelOf (Names.user f) l`, and a return label
`.L{fn}.x{k}` of a user function `fn`); no runtime run's label does. -/
def WcL (L : Label) : Prop := L.toList.take 5 = ".Lwc_".toList

instance : DecidablePred WcL := fun L => inferInstanceAs (Decidable (L.toList.take 5 = ".Lwc_".toList))

/-- **A piece of a block's code at `pc` off the write abort's labels, in a
user function's run**: the code predicate `CdC` at a label `L` none of
`abLabs` beginning `.Lwc_` (`WcL`), so no runtime run's piece (e.g. `print`'s
loop, whose `jmp` enters the write abort): `CdCQ` at those labels, each of
its pieces after one (a checked `+`'s or a `ret`'s fresh label, P5). -/
def CdCL (cells : List (Directive × Nat)) (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64)
    (ra : Int64) (pc : Int64) (blk : List (Directive × Nat)) : Prop :=
  CdCQ (fun L => L ∉ abLabs ∧ WcL L) cells okPc ph lab ra pc blk

theorem CdCL.toCdC {cells : List (Directive × Nat)} {okPc : Nat → Bool} {ph : Nat → Nat}
    {lab : Label → Int64} {ra pc : Int64} {blk : List (Directive × Nat)} (h : CdCL cells okPc ph lab ra pc blk) :
    CdC cells okPc ph lab ra pc blk :=
  CdCQ.toCdC h

theorem SubCd.mono {Cd Cd' : Int64 → List (Directive × Nat) → Prop} (hm : ∀ pc blk, Cd pc blk → Cd' pc blk)
    {pc : Int64} {blk : List (Directive × Nat)} (h : SubCd Cd pc blk) : SubCd Cd' pc blk :=
  let ⟨pc0, pre, post, hc, he⟩ := h
  ⟨pc0, pre, post, hm _ _ hc, he⟩

/-- **A cell of a part of the code off the write abort's labels is at a
position off the write abort.** -/
theorem posOff_of_subCdL {cells : List (Directive × Nat)} {okPc : Nat → Bool} {ph : Nat → Nat}
    {lab : Label → Int64} {ra pc : Int64} {blk : List (Directive × Nat)}
    (h : SubCd (CdCL cells okPc ph lab ra) pc blk) {i : Nat} (hi : i < blk.length) :
    PosOff cells lab (pc + Int64.ofNat (cellOff blk i)) := by
  obtain ⟨pc0, pre, post, hc, hpc⟩ := h
  obtain ⟨-, hat, -⟩ := CdCQ.sub (Q := fun L => L ∉ abLabs ∧ WcL L) hc hpc
  have h1 : ∀ q b, At1Q (fun L => L ∉ abLabs ∧ WcL L) cells lab q b → ∀ i < b.length,
      PosOff cells lab (q + Int64.ofNat (cellOff b i)) := by
    rintro q b ⟨L, j, off, hL, hq, hb⟩ i hi
    have := posOff_of_blockAt (lab := lab) hb hL.1 hi
    rwa [Int64.ofNat_add, ← Int64.add_assoc, hq] at this
  rcases hat with h | ⟨b1, b2, rfl, ha1, ha2⟩
  · exact h1 _ _ h i hi
  · by_cases hi1 : i < b1.length
    · have e : cellOff (b1 ++ b2) i = cellOff b1 i := by
        unfold cellOff; rw [List.take_append_of_le_length (by omega)]
      rw [e]; exact h1 _ _ ha1 i hi1
    · have e : cellOff (b1 ++ b2) i = (b1.map (·.2)).sum + cellOff b2 (i - b1.length) := by
        unfold cellOff
        rw [List.take_append, List.take_of_length_le (by omega), List.map_append, List.sum_append]
      rw [e, Int64.ofNat_add, ← Int64.add_assoc]
      exact h1 _ _ ha2 _ (by simp at hi; omega)

/-! ## The consumers' `hab` -/

/-- **A part of the code off the write abort's labels keeps the write
abort's phase** (`blkW_abSt_pos`): covered at its node's offsets (`hok`),
with no `ret` (`hnr`), the pc right after it a position off the write
abort (`hend`, e.g. `posOff_of_subCdL` at a longer part), and every target
other than a cell's fall-through a position off the write abort or, for a
`call scc_rt_abort`, reached at `%rdi ≠ 4` (`htgt`). -/
theorem blkW_abSt_subCdL {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
    {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat}
    (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    {R : Region} {F : MachineData → Prop} {n : ND} {blk : List (Directive × Nat)} {lo hi : Int} {ra : Int64}
    (hcd : SubCd (CdCL cells okPc ph lab ra) n.pc blk) (hok : okBlk lo hi n.o blk = true)
    (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hnr : noRetBlk blk = true) (hend : PosOff cells lab (n.pc + Int64.ofNat (cellOff blk blk.length)))
    (htgt : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) a, classify blk[k].1 = some a →
      ∀ t ∈ aiTgts lab (n.pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2) ra a,
        t ≠ n.pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2 →
        PosOff cells lab t ∨
          (a = .call "scc_rt_abort" ∧ (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.get64 .rdi ≠ 4#64)) :
    BlkW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n blk := by
  have hcd' := hcd
  obtain ⟨pc0, pre, post, hc0, hpc⟩ := hcd'
  obtain ⟨-, hat, hrun⟩ := CdCQ.sub (Q := fun L => L ∉ abLabs ∧ WcL L) hc0 hpc
  have hph := Scc.Cert.Ph1X64.blkPh_of_runPhB (xs := []) (zs := []) (by simpa using hrun)
    (classify_of_okBlk hok)
  simp only [List.nil_append, List.append_nil, List.length_nil] at hph
  rw [show cellOff blk 0 = 0 by simp [cellOff], show Int64.ofNat 0 = 0 from rfl, Int64.add_zero] at hph
  have h1 : ∀ pc b, At1Q (fun L => L ∉ abLabs ∧ WcL L) cells lab pc b →
      ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s pc b := by
    rintro _ _ ⟨L, j, off, -, hpc', hb⟩ s hs hn
    have := Scc.Cert.Rt.X64.codeAt_blockAt_lays hI.lays hs (hn.trans hI.endOk) hb
    rwa [hI.labOk, hpc'] at this
  have hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk := by
    rcases hat with h | ⟨b1, b2, rfl, ha1, ha2⟩
    · exact h1 _ _ h
    · exact fun s hs hn => Spike.Lib.X64.CodeAt.append (h1 _ _ ha1 s hs hn) (h1 _ _ ha2 s hs hn)
  refine blkW_abSt_pos hI hpr hab hcode hok hR hlo hhi hph hnr ?_
  intro σ c hJ k hk a ha t ht
  by_cases hf : t = n.pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2
  · refine .inl ?_
    have hf' : t = n.pc + Int64.ofNat (cellOff blk (k + 1)) := by
      rw [hf, cellOff_succ hk, Int64.ofNat_add, Int64.add_assoc]
    rw [hf']
    rcases Nat.lt_or_ge (k + 1) blk.length with h1 | h1
    · exact posOff_of_subCdL hcd h1
    · rw [show k + 1 = blk.length by omega]
      exact hend
  · exact htgt σ c hJ k hk a ha t ht hf

/-- **An instruction falling through to the next** (a load, a store, a push,
a pop or a register operation). -/
def fallI : AI → Bool
  | .ld .. | .st .. | .push .. | .pop .. | .reg .. => true
  | _ => false

/-- **A block of fall-throughs**: every cell covered, a load, a store, a
push, a pop or a register operation. -/
def fallBlk (blk : List (Directive × Nat)) : Bool :=
  blk.all fun dz => match classify dz.1 with
    | some a => fallI a
    | none => false

theorem fallBlk_get {blk : List (Directive × Nat)} (h : fallBlk blk = true) {k : Nat} (hk : k < blk.length)
    {a : AI} (ha : classify blk[k].1 = some a) : fallI a = true := by
  have := List.all_eq_true.mp h _ (List.getElem_mem hk)
  simp only [ha] at this
  exact this

theorem noRetBlk_of_fallBlk {blk : List (Directive × Nat)} (h : fallBlk blk = true) : noRetBlk blk = true := by
  unfold noRetBlk
  refine List.all_eq_true.mpr fun d hd => ?_
  have := List.all_eq_true.mp h d hd
  split
  · next hr => simp only [hr] at this; cases this
  · rfl

/-- **A block of fall-throughs off the write abort's labels keeps the write
abort's phase** (`blkW_abSt_subCdL`, no other target): the pc right after it
a position off the write abort (`hend`). -/
theorem blkW_abSt_fallL {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
    {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat}
    (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    {R : Region} {F : MachineData → Prop} {n : ND} {blk : List (Directive × Nat)} {lo hi : Int} {ra : Int64}
    (hcd : SubCd (CdCL cells okPc ph lab ra) n.pc blk) (hok : okBlk lo hi n.o blk = true)
    (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hf : fallBlk blk = true) (hend : PosOff cells lab (n.pc + Int64.ofNat (cellOff blk blk.length))) :
    BlkW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n blk := by
  refine blkW_abSt_subCdL hI hpr hab hcd hok hR hlo hhi (noRetBlk_of_fallBlk hf) hend ?_
  intro σ c hJ k hk a ha t ht hne
  have := fallBlk_get hf hk ha
  cases a <;> simp only [fallI, Bool.false_eq_true] at this <;>
    simp only [aiTgts, List.mem_singleton] at ht <;> exact absurd ht hne

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.blkW_abSt_subCdL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkW_abSt_subCdL

/-- info: 'Spike.Lib.LowerX64.blkW_abSt_fallL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkW_abSt_fallL

end Spike.Lib.LowerX64
