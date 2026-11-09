/-
**`scc_rt_thread_reserve` with the counter's owned value at the node's
states** (x86-64): `reserve_segW` with `ResOk.own` (`OwnAt`, every state at
the counter's `lock xadd`) weakened to the `lock xadd` node's states
(`ResOkA.own`), as `X64RtTcbGA` does for `scc_rt_alloc_tcb`. The x86-64
twin of `Spike/Lib/Rt/A64RtReserveA.lean`.

- `ResOkA`, `ResOkA.of_resOk`, `ResOkA.mono`;
- `reserve_segWA`: `reserve_segW` at `ResOkA`.
-/
import Spike.Lib.Rt.X64RtReserve
import Spike.Lib.Rt.X64RtTcbGA

namespace Spike.Lib.X64.Rt.Reserve

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib.X64 Spike.Lib.X64.Flow Spike.Lib.X64.Flow.Ret0
open Spike.Lib.X64.Flow.Reserve
open Spike.Lib.X64.Flow.Ret0.AllocTcb (G siAt)
open Scc.Cert.Rt.X64 (Lays endOf blockAtB labelGapB code_field label_labelGapB)
open Spike.Lib.X64Consumer
open Spike.Lib.X64.Rt

set_option linter.unusedSimpArgs false

/-- **The counter's add at `q`, owned at the `lock xadd` node's states**
(`ResOk` with `own` at `rvN q .rmw`'s states in the callee's region `R`
under its frame condition `F`). -/
structure ResOkA (ms : MemSide isa) (F0 : MachineData → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (q : ResG) : Prop where
  next : StOk ms F0 (ntA (_root_.Executable.labels exe).label) (q.n + 1#64)
  own : ∀ s c, At exe endPc R F (rvN (_root_.Executable.labels exe).label q .rmw) s c →
    (⟨ntA (_root_.Executable.labels exe).label, 8⟩, q.n.setWidth 128) ∈ ms.own s

/-- `ResOk` (owned at every state at the pc) gives `ResOkA`. -/
theorem ResOkA.of_resOk {ms : MemSide isa} {F0 F : MachineData → Prop} {exe : _root_.Executable}
    {endPc : Int64} {R : Region} {q : ResG} (h : ResOk ms F0 exe endPc q.n) : ResOkA ms F0 exe endPc R F q :=
  ⟨h.next, fun s _ hA => h.own s hA.1 hA.2.1 hA.2.2.2.1⟩

/-- `ResOkA` under a stronger frame condition. -/
theorem ResOkA.mono {ms : MemSide isa} {F0 F F' : MachineData → Prop} {exe : _root_.Executable}
    {endPc : Int64} {R : Region} {q : ResG} (h : ResOkA ms F0 exe endPc R F q) (hFF : ∀ m, F' m → F m) :
    ResOkA ms F0 exe endPc R F' q :=
  ⟨h.next, fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => h.own s c ⟨he, hn, hdc, hpc, σ, hA, hFF _ hD, hJ⟩⟩

section SegProof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {cells : List (Directive × Nat)}
  {R : Region} {F F0 : MachineData → Prop}

set_option hygiene false in
/-- A block node of `scc_rt_thread_reserve` inside `W`: the block, its
`okBlk`, its code, its obligation; the edge is left. -/
local macro "rnodeW " b:ident ok:ident hb:term:max w:term:max : tactic =>
  `(tactic| refine seg_ndW (by simp [$b:ident]) $ok hF hR hlo hhi
    (code_field hp hend $hb (by first | rfl | exact ofNat_zero' _)) $w fun σ c hJ => ⟨c, .refl c, ?_⟩)

set_option hygiene false in
/-- `rnodeW` for `rRet`, split by its return label `retL` after 3 rows
(`blockAcrossB`, `Spike.Lib.X64.code_field_blockAcrossB`). -/
local macro "rnodeWX " b:ident ok:ident hb:term:max w:term:max : tactic =>
  `(tactic| refine seg_ndW (by simp [$b:ident]) $ok hF hR hlo hhi
    (Spike.Lib.X64.code_field_blockAcrossB hp hend $hb (List.take_append_drop 3 _)
      (by first | rfl | exact ofNat_zero' _)) $w fun σ c hJ => ⟨c, .refl c, ?_⟩)

/-- **`scc_rt_thread_reserve` is one segment inside `W`, the counter owned
at the `lock xadd` node's states** (`reserve_segW` at `ResOkA`). -/
theorem reserve_segWA {W : Frag isa} {K : State → State → Prop} {kp : Nat}
    (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp) (hin : reserveIn cells = true)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -40) (hhi : 8 ≤ R.hi)
    (hFF : ∀ m, F m → F0 m) (q : ResG) (hn : q.n.toNat + 1 ≤ 1023)
    (hres : ResOkA ms F0 exe endPc R F q) (hW : ∀ i, ReserveW W K exe endPc R F q i) :
    SegW W K p lbl ms (At exe endPc R F (rvN (_root_.Executable.labels exe).label q .e))
      (fun s c => ∃ x, At exe endPc R F (rvX q x) s c) := by
  have h := hin
  simp only [reserveIn, siAt, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hg, bE⟩, bA⟩, bArg⟩, bRmw⟩, bBnd⟩, bJ⟩, bOk⟩ := h
  have eEntry := label_labelGapB hp hg
  refine fn_segW (N := rvN _ q) (E := rvX q) (fun i => ?_) RN.e
  cases i
  case e =>
    rnodeW rPro rPro_ok bE (hW RN.e)
    dsimp only [rvN, rvX] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := rPro_walk (_root_.Executable.labels exe).label _ hJ
    exact .inl ⟨RN.entry, by rw [h1]; exact eEntry, by rw [h2]; rfl, rfl, h3⟩
  case entry =>
    refine si_ndW (si := .leaRip .rax "scc_rt_nthreads") (z := 7) rfl hF
      (code_field hp hend bA (ofNat_zero' _)) (hW RN.entry)
      fun σ c hJ => ⟨c, .refl c, .inl ⟨RN.arg, rfl, rfl, ?_⟩⟩
    obtain ⟨rfl, hJ⟩ := hJ
    exact ⟨rfl, si_fr _ _ hJ, si_rax _ _ σ⟩
  case arg =>
    rnodeW rArg rArg_ok bArg (hW RN.arg)
    dsimp only [rvN, rvX] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := rArg_walk (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨RN.rmw, by rw [h1]; exact ofNat_add' _ 7 15, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case rmw =>
    refine ownXadd_ndWA (b := .rcx) (k := 0) (r := .rax) (z := 5) (by decide) hF
      (code_field hp hend bRmw rfl) hres.own (hW RN.rmw) fun m σ c _ hD hJ => ?_
    dsimp only [rvN] at hJ ⊢
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    have hb : bAddr σ.regs .rcx 0 = ntA (_root_.Executable.labels exe).label := by
      rw [← hc]; simp [bAddr, Reg64s.get64]
    have hv : σ.regs.get64 .rax = 1#64 := by rw [← ha]; rfl
    rw [hb, hv]
    exact ⟨rfl, hres.next.rt, hres.next.mp, hres.next.G, hres.next.unmapped m (hFF m hD),
      q.c0, .refl q.c0, fun fl =>
        .inl ⟨RN.bnd, ofNat_add' _ 22 5, rfl, rfl, by simpa [ownStep, Flow.Reserve.Fr, Reg64s.set64] using hJ,
          by simp [ownStep, Reg64s.set64]⟩⟩
  case bnd =>
    rnodeW rBnd rBnd_ok bBnd (hW RN.bnd)
    dsimp only [rvN, rvX] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := rBnd_walk (_root_.Executable.labels exe).label _ hJ ha hn
    exact .inl ⟨RN.j, by rw [h1]; exact ofNat_add' _ 27 38, by rw [h2]; rfl, rfl, h3⟩
  case j =>
    rnodeW rJ rJ_ok bJ (hW RN.j)
    dsimp only [rvN, rvX] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := rJ_walk (_root_.Executable.labels exe).label _ hJ
    exact .inl ⟨RN.ok, h1.symm, by rw [h2]; rfl, rfl, h3⟩
  case ok =>
    rnodeWX rRet rRet_ok bOk (hW RN.ok)
    dsimp only [rvN, rvX] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := rRet_walk (_root_.Executable.labels exe).label _ hJ
    exact .inr ⟨(), h1.symm, by rw [h2]; rfl, rfl, h3⟩

end SegProof

end Spike.Lib.X64.Rt.Reserve

/-- info: 'Spike.Lib.X64.Rt.Reserve.ResOkA.of_resOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.Reserve.ResOkA.of_resOk

/-- info: 'Spike.Lib.X64.Rt.Reserve.ResOkA.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.Reserve.ResOkA.mono

/-- info: 'Spike.Lib.X64.Rt.Reserve.reserve_segWA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.Reserve.reserve_segWA
