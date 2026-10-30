/-
**Functions with the load-or-stutter row inside a state predicate**
(AArch64): `Spike/Lib/A64CfgL.lean`'s combinators over `SegLW W`
(`Spike/Lib/SegLW.lean`).

- `seg_fixLW`, `seg_movedLW`, `fn_seg_gLW`: a node of a fixed frame, a given
  node that moves the frame, a whole function whose frame may move.
- `ldarSt_ndW`: the acquire load's node with the load-or-stutter row, its
  state in `W` (`hW`).
- `blk_exec_done`, `blk_notLdAt`: a covered block's internal states run to
  `.done`, so they load nothing (`NotLdAt`, for `seg_ndW`'s `hW`).
-/
import Spike.Lib.A64CfgL
import Spike.Lib.SegLW
import Spike.Lib.A64Cfg
import Spike.Lib.A64AbOffLDef

namespace Spike.Lib.A64.Flow

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem (ValRep)
open Spike.Lib.A64.Flow.Ret0 (land_ldStep)

section MovingLW

variable {W : Frag isaLSE2} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {γ ι κ : Sort _} {Rg : γ → Region} {Fg : γ → MachineData → Prop}
  {N : γ → ι → ND} {E : γ → κ → ND}

/-- **A node of a fixed frame inside `W`**, with the load-or-stutter row. -/
theorem seg_fixLW {P : Frag isaLSE2} (g : γ) (h : SegLW W p lbl ms P (Next exe endPc (Rg g) (Fg g) (N g) (E g))) :
    SegLW W p lbl ms P (NextG exe endPc Rg Fg N E) :=
  h.mono_post fun _ _ h => h.elim (fun ⟨j, h⟩ => .inl ⟨g, j, h⟩) fun ⟨x, h⟩ => .inr ⟨g, x, h⟩

/-- **A given node that moves the frame, inside `W`**, with the
load-or-stutter row. -/
theorem seg_movedLW {P : Frag isaLSE2} (j : ι)
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

section LdarW

variable {W : Frag isaLSE2} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND}
  {E : κ → ND}

/-- **`ldarSt_nd` inside `W`**: the node's states are in `W` (`hW`). -/
theorem ldarSt_ndW {n : ND} {t b : XReg} {A : BitVec 64} {V : Nat} (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [ldarDir t b])
    (hdm : ∀ m, F m → Mem.loadInt m.dmem A 8 = none)
    (hW : ∀ s c, At exe endPc R F n s c → W s c)
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      (σ.regs.getXReg b).toBitVec = A ∧
      ∃ x a e ty w, c.term = .let_ x (.load true a) e ∧ TermRun.evalAt c.env a = some (ty, [w]) ∧
        ValRep lbl w.val A.toNat ∧ (∃ sa, w.val = .loc sa 0) ∧
        (∀ v : BitVec 64, v.toNat ≠ V → Lands N E ⟨n.pc + Int64.ofNat 4, n.o.kill t, ldStep t v σ⟩ c) ∧
        (∀ (v : BitVec 64) (w' : TermRun.Word), v.toNat = V → ms.rd w' → ValRep lbl w'.val V →
          Lands N E ⟨n.pc + Int64.ofNat 4, n.o.kill t, ldStep t v σ⟩ ⟨e, (x, loadTy ty, [w']) :: c.env, none⟩)) :
    SegLW W p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine SegLW.step hW fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ?_
  have hc : CellAt s (ldarDir t b) 4 := (hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
  obtain ⟨hb, x, a, e, ty, w, ht, hev, hv, htag, hne, heq⟩ := hedge _ σ c hA hD hJ
  have hb' : (s.st.1.regs.getXReg b).toBitVec = A := by rw [hA.regs]; exact hb
  have hex := exec_ldar_agrees hc (by rw [hb']; exact hdm _ hD) (agrees_of_decls hdc _ _)
  rw [hb'] at hex
  refine .ldSt .acq A _ x a e ty w V hex ht hev hv (fun v hvV => ?_) (fun v w' hvV hr hr' => ?_) htag
  · exact land_ldStep hF he hn hdc hpc hA hD (hne _ hvV)
  · exact land_ldStep hF he hn hdc hpc hA hD (heq _ w' hvV hr hr')

end LdarW

section BlkDone

/-- **A covered block's internal states run to `.done`**: before its `k`-th
instruction, the machine data related to the abstract run of the first `k`
instructions. -/
theorem blk_exec_done {R : Region} {lo hi : Int} {o : SO} {blk : List Directive} {pc : Int64}
    (hok : okBlk lo hi o blk = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo)
    (hhi : hi ≤ R.hi) {s : State} (hcode : CodeAt s pc blk) {σ : AS} {k : Nat} (hk : k < blk.length)
    {m : MachineData}
    (hA : Abs R (arun (labA s) (blk.take k) ⟨pc, o, σ⟩).so m (arun (labA s) (blk.take k) ⟨pc, o, σ⟩).σ) :
    ∃ s', isaLSE2.exec { s with st := (m, pc + Int64.ofNat (4 * k)) } = some (.done s') := by
  have hd : blk[k]? = some blk[k] := List.getElem?_eq_getElem hk
  obtain ⟨a, hca, haok, -⟩ := okBlk_get (labA s) (am := ⟨pc, o, σ⟩) hok hk
  obtain ⟨hdir, hreg⟩ := classify_sound hca
  have hc : CellAt { s with st := (m, pc + Int64.ofNat (4 * k)) } a.toDir 4 :=
    hcode.cell (j := k) (hdir ▸ hd) rfl rfl rfl
  obtain ⟨m', hex, -, -⟩ := exec_ai haok hR hal hlo hhi hc hreg hA
  exact ⟨_, hex⟩

/-- **A covered block's internal states load nothing at `A`** (in
`seg_ndW`'s `hW` form). -/
theorem blk_notLdAt {exe : _root_.Executable} {R : Region} {lo hi : Int} {o : SO} {blk : List Directive}
    {pc : Int64} (hok : okBlk lo hi o blk = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo)
    (hhi : hi ≤ R.hi) {s : State} (he : s.exe = exe) (hcode : CodeAt s pc blk) {σ : AS} {k : Nat}
    (hk : k < blk.length) {m : MachineData}
    (hA : Abs R (arun (_root_.Executable.labels exe).label (blk.take k) ⟨pc, o, σ⟩).so m
      (arun (_root_.Executable.labels exe).label (blk.take k) ⟨pc, o, σ⟩).σ) (A : BitVec 64) :
    Spike.Lib.A64AbOffL.NotLdAt A { s with st := (m, pc + Int64.ofNat (4 * k)) } := by
  subst he
  obtain ⟨s', h⟩ := blk_exec_done hok hR hal hlo hhi hcode hk hA
  exact Spike.Lib.A64AbOffL.notLdAt_of_done h

end BlkDone

end Spike.Lib.A64.Flow
