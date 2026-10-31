/-
**Functions with the load-or-stutter row inside a state predicate**
(x86-64): `Spike/Lib/X64CfgL.lean`'s combinators over `SegLW W`
(`Spike/Lib/SegLW.lean`). The x86-64 twin of `Spike/Lib/A64CfgLW.lean`.

- `seg_fixLW`, `seg_movedLW`, `fn_seg_gLW`: a node of a fixed frame, a given
  node that moves the frame, a whole function whose frame may move.
- `ldSt_ndW`: the spin-wait load's node (`ldSt_nd`) with the load-or-stutter
  row, its state in `W` (`hW`).
- `blk_exec_done`, `blk_notLdAt`: a covered block's internal states run to
  `.done`, so they load nothing (`NotLdAt`, for `seg_ndW`'s `hW`).

Where x86-64 differs from AArch64: instructions have their cells' sizes (the
`k`-th at `pc + cellOff blk k`), and `exec_ai` needs no alignment.
-/
import Spike.Lib.X64CfgL
import Spike.Lib.SegLW
import Spike.Lib.X64AbOffLDef

namespace Spike.Lib.X64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Scc.Sem (ValRep)

section MovingLW

variable {W : Frag isa} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {γ ι κ : Sort _} {Rg : γ → Region} {Fg : γ → MachineData → Prop}
  {N : γ → ι → ND} {E : γ → κ → ND}

/-- **A node of a fixed frame inside `W`**, with the load-or-stutter row. -/
theorem seg_fixLW {P : Frag isa} (g : γ) (h : SegLW W p lbl ms P (Next exe endPc (Rg g) (Fg g) (N g) (E g))) :
    SegLW W p lbl ms P (NextG exe endPc Rg Fg N E) :=
  h.mono_post fun _ _ h => h.elim (fun ⟨j, h⟩ => .inl ⟨g, j, h⟩) fun ⟨x, h⟩ => .inr ⟨g, x, h⟩

/-- **A given node that moves the frame, inside `W`**, with the
load-or-stutter row. -/
theorem seg_movedLW {P : Frag isa} (j : ι)
    (h : SegLW W p lbl ms P (fun s c => ∃ g, At exe endPc (Rg g) (Fg g) (N g j) s c)) :
    SegLW W p lbl ms P (NextG exe endPc Rg Fg N E) :=
  h.mono_post fun _ _ ⟨g, h⟩ => .inl ⟨g, j, h⟩

/-- **A whole function whose frame may move, inside `W`**, with the
load-or-stutter row. -/
theorem fn_seg_gLW (h : ∀ g i, SegLW W p lbl ms (At exe endPc (Rg g) (Fg g) (N g i)) (NextG exe endPc Rg Fg N E))
    (g0 : γ) (i0 : ι) :
    SegLW W p lbl ms (At exe endPc (Rg g0) (Fg g0) (N g0 i0))
      (fun s c => ∃ g x, At exe endPc (Rg g) (Fg g) (E g x) s c) :=
  (SegLW.cfg (fun gi : PProd γ ι => At exe endPc (Rg gi.1) (Fg gi.1) (N gi.1 gi.2)) fun gi =>
      (h gi.1 gi.2).mono_post fun _ _ h => h.elim (fun ⟨g, j, h⟩ => .inl ⟨⟨g, j⟩, h⟩) .inr).mono_pre
    fun _ _ h => ⟨⟨g0, i0⟩, h⟩

end MovingLW

section LdStW

variable {W : Frag isa} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND}
  {E : κ → ND}

/-- **`ldSt_nd` inside `W`**: the node's states are in `W` (`hW`). -/
theorem ldSt_ndW {n : ND} {b r : Reg64} {k : Int64} {z : Nat} {A : BitVec 64} {V : Nat} (hr : r ≠ .rsp)
    (hF : FStable R F) (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(ldDir b k r, z)])
    (hdm : ∀ m, F m → Mem.loadInt m.dmem A 8 = none)
    (hW : ∀ s c, At exe endPc R F n s c → W s c)
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      bAddr σ.regs b k = A ∧
      ∃ x a e ty w, c.term = .let_ x (.load true a) e ∧ TermRun.evalAt c.env a = some (ty, [w]) ∧
        ValRep lbl w.val A.toNat ∧ (∃ sa, w.val = .loc sa 0) ∧
        (∀ v : BitVec 64, v.toNat ≠ V → Lands N E ⟨n.pc + Int64.ofNat z, n.o.kill r, ownStep r v σ⟩ c) ∧
        ∀ (v : BitVec 64) (w' : TermRun.Word), v.toNat = V → ms.rd w' → ValRep lbl w'.val V →
          Lands N E ⟨n.pc + Int64.ofNat z, n.o.kill r, ownStep r v σ⟩ ⟨e, (x, loadTy ty, [w']) :: c.env, none⟩) :
    SegLW W p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine SegLW.step hW fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ?_
  have hc : CellAt s (ldDir b k r) z := (hcode s he hn).cell0 rfl rfl hpc
  obtain ⟨hb, x, a, e, ty, w, ht, hev, hv, htag, hne, heq⟩ := hedge _ σ c hA hD hJ
  have ha' : eaddr s z (mB b k) = A := (eaddr_mB s z b k).trans (by rw [hA.regs]; exact hb)
  have hex := exec_load_agrees hc ha' (hdm _ hD) (agrees_of_decls hdc _ _)
  refine .ldSt .plain A _ x a e ty w V hex ht hev hv (fun v hvV => ?_) (fun v w' hvV hr' hr'' => ?_) htag
  · exact land_own (flm := s.st.1.status) (fla := σ.status) hA.status hr hF he hn hdc hpc hA hD (hne _ hvV)
  · exact land_own (flm := s.st.1.status) (fla := σ.status) hA.status hr hF he hn hdc hpc hA hD
      (heq _ w' hvV hr' hr'')

end LdStW

section BlkDone

/-- **A covered block's internal states run to `.done`**: before its `k`-th
instruction (at `pc + cellOff blk k`), the machine data related to the
abstract run of the first `k` instructions. -/
theorem blk_exec_done {R : Region} {lo hi : Int} {o : SO} {blk : List (Directive × Nat)} {pc : Int64}
    (hok : okBlk lo hi o blk = true) (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi) {s : State}
    (hcode : CodeAt s pc blk) {σ : AS} {k : Nat} (hk : k < blk.length) {m : MachineData}
    (hA : Abs R (arun (labelAddr s) (blk.take k) ⟨pc, o, σ⟩).so m
      (arun (labelAddr s) (blk.take k) ⟨pc, o, σ⟩).σ) :
    ∃ s', isa.exec { s with st := (m, pc + Int64.ofNat (cellOff blk k)) } = some (.done s') := by
  obtain ⟨a, hca, haok, -⟩ := okBlk_get (labelAddr s) (am := ⟨pc, o, σ⟩) hok hk
  obtain ⟨hdir, hreg⟩ := classify_sound hca
  have hd : blk[k]? = some (a.toDir, blk[k].2) := by rw [List.getElem?_eq_getElem hk, ← hdir]
  have hc : CellAt { s with st := (m, pc + Int64.ofNat (cellOff blk k)) } a.toDir blk[k].2 :=
    hcode.cell hd rfl rfl rfl
  obtain ⟨m', hex, -, -⟩ := exec_ai haok hR hlo hhi hc hreg hA
  exact ⟨_, hex⟩

/-- **A covered block's internal states load nothing at `A`** (in
`seg_ndW`'s `hW` form). -/
theorem blk_notLdAt {exe : _root_.Executable} {R : Region} {lo hi : Int} {o : SO} {blk : List (Directive × Nat)}
    {pc : Int64} (hok : okBlk lo hi o blk = true) (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi) {s : State}
    (he : s.exe = exe) (hcode : CodeAt s pc blk) {σ : AS} {k : Nat} (hk : k < blk.length) {m : MachineData}
    (hA : Abs R (arun (_root_.Executable.labels exe).label (blk.take k) ⟨pc, o, σ⟩).so m
      (arun (_root_.Executable.labels exe).label (blk.take k) ⟨pc, o, σ⟩).σ) (A : BitVec 64) :
    Spike.Lib.X64AbOffL.NotLdAt A { s with st := (m, pc + Int64.ofNat (cellOff blk k)) } := by
  subst he
  obtain ⟨s', h⟩ := blk_exec_done hok hR hlo hhi hcode hk hA
  exact Spike.Lib.X64AbOffL.notLdAt_of_done h

end BlkDone

end Spike.Lib.X64

/-- info: 'Spike.Lib.X64.blk_notLdAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.blk_notLdAt
