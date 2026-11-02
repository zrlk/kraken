/-
**wake.w's ghost records' facts at the x86-64 instance** (x86-64 twin of `Spike/Lib/WakeOkW.lean`): the concrete `ok` of
`X64WakeInst`'s ghost records `Gh` for wake.w, and the record the spawn
obligation builds at main's clone, with the proof that it satisfies `ok`.

- `okW Λ lbl' cSf g`: `X64WakeInstFields.GhOK Λ g` (pointer words, source
  memory nonempty, the flag's word placed and shared), the spawn's
  placement the worker side's `lbl'` and the flag the side's `cSf`.
- `okW_ghOK`, `okW_lbl`, `okW_cS`, and the worker side's premises from
  `g.2`: `okW_hcw`, `okW_cT`, `okW_cTin`, `okW_Spos`, `okW_hflag`.
- `recW`: the record built at the clone (`cS := ⟨l, 0⟩`, `c`'s label;
  main's pointer word `cst (.loc ⟨l, 0⟩ 0)`; `cT` the word placed for it).
- `okW_of_clone`: `recW` satisfies `okW`, from the memory relation at the
  spawn (`MemRelP`, for `cTin`), the layout well formed, `c`'s `ValRep`;
  open: `hin` (`c`'s label holds a word), `hS` (source memory nonempty),
  `hlbl`, `hcS`.
- `clonePre_c`, `okW_of_clonePre`: `c`'s label and `ValRep` (at `%r12`)
  taken from `X64WakePreA.ClonePre`.
- `okW_sat`: `okW` is satisfiable at any placement holding a shared word
  for `cSf` (it is not vacuous).

**Where this differs from AArch64**: `c`'s target address is in `%r12`
(A64 `x9`) and `ClonePre` has no label prefix; `c`'s binding is read off
`ClonePre` here (`clonePre_c`) rather than through the worker side's
`clonePre_cw` (A64 `WakeWorkerSide`, not imported: the x86-64 worker side
is a later module). The open premises are A64's (`hin`, `hS`, `hlbl`,
`hcS`).
-/
import Spike.Lib.X64WakeInstFields
import Spike.Lib.X64WakePreA

namespace Spike.Lib.X64WakeOkW

open Kraken.Promising Kraken.Promising.X64 Scc.Sem
open Spike.Lib Spike.Lib.X64WakeInst
open Spike.Lib.X64WakeInstFields (GhOK)

/-- **wake.w's ghost records' facts**: `GhOK`, the spawn's placement the
worker side's labels `lbl'`, the flag its `cSf`. -/
def okW (Λ : Scc.Sem.Layout) (lbl' : WeakMem.AllocLabel → Option Nat) (cSf : WeakMem.Address) (g : Gh) : Prop :=
  GhOK Λ g ∧ g.lbl = lbl' ∧ g.cS = cSf

section Proj

variable {Λ : Scc.Sem.Layout} {lbl' : WeakMem.AllocLabel → Option Nat} {cSf : WeakMem.Address}
  (w : {g : Gh // okW Λ lbl' cSf g})

theorem okW_ghOK : GhOK Λ w.1 := w.2.1
theorem okW_lbl : w.1.lbl = lbl' := w.2.2.1
theorem okW_cS : w.1.cS = cSf := w.2.2.2

/-- The worker's word is an untagged locative to the flag (`WCompat.cwv`). -/
theorem okW_hcw : w.1.cwW.val = .loc w.1.cS 0 := w.2.1.2.1

/-- The worker side's `cT`. -/
theorem okW_cT : ∃ a, w.1.cT = wordLoc a ∧ wordAddr w.1.lbl w.1.cS = some a ∧
    w.1.cS.offset < w.1.lsize w.1.cS.label := by
  obtain ⟨b, hl, ho, hT⟩ := w.2.1.2.2.2.1
  exact ⟨_, hT, by simp [wordAddr, hl], ho⟩

/-- The worker side's `cTin`. -/
theorem okW_cTin : Consumer1.LocIn Λ.shared w.1.cT := w.2.1.2.2.2.2

/-- The worker side's `Spos`. -/
theorem okW_Spos : 0 < w.1.S := w.2.1.2.2.1

/-- The child segment's `hflag` (at `lbl := w.1.lbl`). -/
theorem okW_hflag : ∀ x, wordAddr w.1.lbl cSf = some x → Consumer1.LocIn Λ.shared (wordLoc x) := by
  obtain ⟨a, hT, hA, -⟩ := okW_cT w
  intro x hx
  have hx' : wordAddr w.1.lbl w.1.cS = some x := by rw [okW_cS w]; exact hx
  rw [hA] at hx'
  cases hx'
  rw [← hT]; exact okW_cTin w

end Proj

/-! ## The record built at the clone -/

/-- **The ghost record at main's clone**: the target memory's last message
`T`, the source memory's size `S`, the placement `lbl`/`lsize`, the flag
`c`'s label `l` (offset 0), main's pointer word the constant untagged
locative to it, the worker's `cw`, the flag's word the one placed for it,
main's permit word `pT`. -/
def recW (T S : Nat) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat)
    (l : WeakMem.AllocLabel) (pT : Loc) (cw : TermRun.Word) : Gh where
  T := T
  S := S
  lbl := lbl
  lsize := lsize
  cS := ⟨l, 0⟩
  cT := wordLoc ((lbl l).getD 0 + 8 * 0)
  cwM := TermRun.cst (.loc ⟨l, 0⟩ 0)
  cwW := cw
  pT := pT

/-- **`recW` satisfies `okW`**: `c`'s label placed (its `ValRep`, `hv`), its
word shared (`MemRelP`, the layout's heap and data in the address space),
the worker's word `cw` a locative to it (`hcw`); open: `hin`, `hS`,
`hlbl`, `hcS`. -/
theorem okW_of_clone {Λ : Scc.Sem.Layout} {lbl' : WeakMem.AllocLabel → Option Nat} {cSf : WeakMem.Address}
    {T S : Nat} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {l : WeakMem.AllocLabel} {pT : Loc} {cw : TermRun.Word}
    {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tp tq sp : List Nat}
    (hm : MemRelP Λ lbl lsize ts tm sm tp tq sp) (hwf : Λ.WF)
    {cA : Nat} (hv : ValRep lbl (.loc ⟨l, 0⟩ 0) cA) (hcw : cw.val = .loc ⟨l, 0⟩ 0)
    /- OPEN: `c`'s label holds a word -/ (hin : 0 < lsize l)
    /- (G3) OPEN: the source memory is nonempty at the spawn -/ (hS : 0 < S)
    /- OPEN: the spawn's placement and `c`'s label are the
    worker side's -/ (hlbl : lbl = lbl') (hcS : (⟨l, 0⟩ : WeakMem.Address) = cSf) :
    okW Λ lbl' cSf (recW T S lbl lsize l pT cw) := by
  obtain ⟨-, x, hx, -⟩ := hv
  have hb : lbl l = some x := by
    simp only [wordAddr, Option.map_eq_some_iff] at hx
    obtain ⟨b, hb, hbx⟩ := hx
    simp only [Nat.mul_zero, Nat.add_zero] at hbx
    rw [hb, hbx]
  have hsp : ∀ y, Λ.heap.contains y ∨ Λ.data.contains y → y < 2 ^ 64 := by
    intro y hy
    rcases hy with hy | hy
    · have := (hwf.inSpace Λ.heap (by simp [Layout.regions])).2; unfold Range.contains at hy; omega
    · have := (hwf.inSpace Λ.data (by simp [Layout.regions])).2; unfold Range.contains at hy; omega
  have hT : (recW T S lbl lsize l pT cw).cT = wordLoc (x + 8 * (recW T S lbl lsize l pT cw).cS.offset) := by
    simp [recW, hb]
  refine ⟨X64WakeInstFields.ghOK_of (g := recW T S lbl lsize l pT cw) hm hsp rfl hcw hS hb hin hT, hlbl, hcS⟩

/-- **`c` at the clone**: main's `c` is bound to the constant untagged
locative `cst (.loc ⟨l, 0⟩ 0)`, which `%r12` represents. -/
theorem clonePre_c {Λ : Scc.Sem.Layout} {r0 r1 : Range} {X : State → Prop}
    {lbl : WeakMem.AllocLabel → Option Nat} {t : X64WakeA64.Cfg} {s : TermRun.Cfg}
    (h : X64WakePreA.ClonePre Λ r0 r1 X lbl t s) :
    ∃ (th0 : TermRun.TTh) (l : WeakMem.AllocLabel) (cA : Nat), s.ths = #[th0] ∧
      TermRun.evalAt th0.env (.var "c") = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) ∧
      ValRep lbl (.loc ⟨l, 0⟩ 0) cA := by
  obtain ⟨-, th0, -, cA, -, l, -, hs, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hc, -, -, hv, -⟩ := h
  exact ⟨th0, l, cA, hs, hc, hv⟩

/-- **`okW_of_clone` from `ClonePre`**: `c`'s label `l` and its `ValRep`
are `ClonePre`'s (`clonePre_c`, the placement `lbl` its). -/
theorem okW_of_clonePre {Λ Λc : Scc.Sem.Layout} {r0 r1 : Range} {X : State → Prop}
    {lbl : WeakMem.AllocLabel → Option Nat} {t : X64WakeA64.Cfg} {s : TermRun.Cfg}
    (h : X64WakePreA.ClonePre Λc r0 r1 X lbl t s) :
    ∃ (th0 : TermRun.TTh) (l : WeakMem.AllocLabel), s.ths = #[th0] ∧
      TermRun.evalAt th0.env (.var "c") = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) ∧
      ∀ {lbl' : WeakMem.AllocLabel → Option Nat} {cSf : WeakMem.Address} {T S : Nat}
        {lsize : WeakMem.AllocLabel → Nat} {pT : Loc} {cw : TermRun.Word}
        {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tp tq sp : List Nat},
        MemRelP Λ lbl lsize ts tm sm tp tq sp → Λ.WF → cw.val = .loc ⟨l, 0⟩ 0 → 0 < lsize l → 0 < S →
        lbl = lbl' → (⟨l, 0⟩ : WeakMem.Address) = cSf → okW Λ lbl' cSf (recW T S lbl lsize l pT cw) := by
  obtain ⟨th0, l, _, hs, hc, hv⟩ := clonePre_c h
  exact ⟨th0, l, hs, hc, fun hm hwf hcw hin hS hlbl hcS => okW_of_clone hm hwf hv hcw hin hS hlbl hcS⟩

/-- **`okW` is satisfiable** at any placement `lbl'` holding a shared word
for `cSf` (offset 0, its label `l` placed at `b`, holding a word). -/
theorem okW_sat {Λ : Scc.Sem.Layout} {lbl' : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {l : WeakMem.AllocLabel} {b : Nat} (hb : lbl' l = some b) (hin : 0 < lsize l)
    (hsh : Consumer1.LocIn Λ.shared (wordLoc b)) (T S : Nat) (hS : 0 < S) (pT : Loc) :
    okW Λ lbl' ⟨l, 0⟩ (recW T S lbl' lsize l pT (TermRun.cst (.loc ⟨l, 0⟩ 0))) := by
  refine ⟨⟨rfl, rfl, hS, ⟨b, hb, hin, by simp [recW, hb]⟩, by simpa [recW, hb] using hsh⟩, rfl, rfl⟩

end Spike.Lib.X64WakeOkW

/-- info: 'Spike.Lib.X64WakeOkW.okW_of_clonePre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeOkW.okW_of_clonePre

/-- info: 'Spike.Lib.X64WakeOkW.okW_hflag' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeOkW.okW_hflag

/-- info: 'Spike.Lib.X64WakeOkW.okW_sat' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeOkW.okW_sat
