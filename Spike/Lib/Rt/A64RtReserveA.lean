/-
**`scc_rt_thread_reserve` with the counter's owned value at the node's
states** (AArch64): `reserve_segW` with `ResOk.own` (`OwnAt`, every state at
the counter's `ldadd`) weakened to the `ldadd` node's states
(`ResOkA.own`), as `A64RtTcbGA` does for `scc_rt_alloc_tcb`.

- `ResOkA`, `ResOkA.of_resOk`, `ResOkA.mono`;
- `reserve_segWA`: `reserve_segW` at `ResOkA`.
-/
import Spike.Lib.Rt.A64RtReserve
import Spike.Lib.Rt.A64RtTcbGA

namespace Spike.Lib.A64.Rt.Reserve

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Ret0
open Spike.Lib.A64.Flow.Reserve
open Scc.Cert.Rt.A64 (Lays endOf blockAt labelGap label_labelGap)
open Spike.Lib.A64Consumer
open Spike.Lib.A64.Rt (ownLdop_ndWA)

set_option linter.unusedSimpArgs false

/-- **The counter's add at `q`, owned at the `ldadd` node's states**
(`ResOk` with `own` at `rvN q .rmw`'s states in the callee's region `R`
under its frame condition `F`). -/
structure ResOkA (ms : MemSide isaLSE2) (F0 : MachineData → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (q : ResG) : Prop where
  next : StOk ms F0 exe endPc (ntA (_root_.Executable.labels exe).label) (q.n + 1#64)
  own : ∀ s c, At exe endPc R F (rvN (_root_.Executable.labels exe).label q .rmw) s c →
    (⟨ntA (_root_.Executable.labels exe).label, 8⟩, q.n.setWidth 128) ∈ ms.own s

/-- `ResOk` (owned at every state at the pc) gives `ResOkA`. -/
theorem ResOkA.of_resOk {ms : MemSide isaLSE2} {F0 F : MachineData → Prop} {exe : _root_.Executable}
    {endPc : Int64} {R : Region} {q : ResG} (h : ResOk ms F0 exe endPc q.n) : ResOkA ms F0 exe endPc R F q :=
  ⟨h.next, fun s _ hA => h.own s hA.1 hA.2.1 hA.2.2.2.1⟩

/-- `ResOkA` under a stronger frame condition. -/
theorem ResOkA.mono {ms : MemSide isaLSE2} {F0 F F' : MachineData → Prop} {exe : _root_.Executable}
    {endPc : Int64} {R : Region} {q : ResG} (h : ResOkA ms F0 exe endPc R F q) (hFF : ∀ m, F' m → F m) :
    ResOkA ms F0 exe endPc R F' q :=
  ⟨h.next, fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => h.own s c ⟨he, hn, hdc, hpc, σ, hA, hFF _ hD, hJ⟩⟩

section SegProof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Spike.Lib.Region} {F F0 : MachineData → Prop}

set_option hygiene false in
/-- A block node of `scc_rt_thread_reserve` inside `W` (`A64RtReserve`'s). -/
local macro "rnodeW " b:ident ok:ident hb:term:max w:term:max : tactic =>
  `(tactic| refine seg_ndW (by simp [$b:ident]) $ok hF hR hal hlo hhi
    (code_of hp hend $hb (by first | rfl | exact ofNat4_zero _)) $w fun σ c hJ => ⟨c, .refl c, ?_⟩)

/-- **`scc_rt_thread_reserve` is one segment inside `W`, the counter owned
at the `ldadd` node's states** (`reserve_segW` at `ResOkA`). -/
theorem reserve_segWA {W : Frag isaLSE2} {K : State → State → Prop} {prog : List Directive} {kp : Nat}
    (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp) (hin : reserveIn prog = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hFF : ∀ m, F m → F0 m) (q : ResG) (hn : q.n.toNat + 1 ≤ 1023)
    (hres : ResOkA ms F0 exe endPc R F q) (hW : ∀ i, ReserveW W K exe endPc R F q i) :
    SegW W K p lbl ms (At exe endPc R F (rvN (_root_.Executable.labels exe).label q .e))
      (fun s c => ∃ x, At exe endPc R F (rvX q x) s c) := by
  have h := hin
  simp only [reserveIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hg, bE⟩, bA⟩, bA1⟩, bArg⟩, bRmw⟩, bBnd⟩, bJ⟩, bOk⟩ := h
  have eEntry := label_labelGap hp hg
  refine fn_segW (N := rvN _ q) (E := rvX q) (fun i => ?_) RN.e
  cases i
  case e =>
    rnodeW rPro rPro_ok bE (hW RN.e)
    dsimp only [rvN, rvX] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := rPro_walk (_root_.Executable.labels exe).label _ hJ
    exact .inl ⟨RN.entry, by rw [h1, ← eEntry]; rfl, by rw [h2]; rfl, rfl, h3⟩
  case entry =>
    refine si_ndW (si := .adrp .X9 "scc_rt_nthreads") hF
      (code_of hp hend bA (ofNat4_zero _)) (hW RN.entry) fun σ c hJ => ⟨c, .refl c, .inl ⟨RN.add, ?_, rfl,
        hJ.1, σ, hJ.2, rfl⟩⟩
    rfl
  case add =>
    refine si_ndW (si := .addLo12 .X9 .X9 "scc_rt_nthreads") hF
      (code_of hp hend bA1 rfl) (hW RN.add) fun σ c hJ => ⟨c, .refl c, .inl ⟨RN.arg, ?_, rfl, ?_⟩⟩
    · exact (ofNat4_succ' _ 1).symm
    · obtain ⟨rfl, σ0, h0, rfl⟩ := hJ
      exact ⟨rfl, labStep_fr0 _ _ h0, (AllocTcb.labStep_spec _ _ σ0).1⟩
  case arg =>
    rnodeW rArg rArg_ok bArg (hW RN.arg)
    dsimp only [rvN, rvX] at hJ ⊢
    obtain ⟨rfl, hJ, h9⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := rArg_walk (_root_.Executable.labels exe).label _ hJ h9
    exact .inl ⟨RN.rmw, by rw [h1, ← ofNat4_add]; rfl, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case rmw =>
    refine ownLdop_ndWA hF (code_of hp hend bRmw rfl) hres.own (hW RN.rmw) fun _ σ c _ _ hJ => ?_
    dsimp only [rvN] at hJ ⊢
    obtain ⟨rfl, hJ, h9, h10⟩ := hJ
    refine ⟨h10, ?_, .inl ⟨RN.bnd, (ofNat4_succ' _ 5).symm, rfl, rfl, ?_, ?_⟩⟩
    · rw [add_apply, getRegOrZr_x9, h9]; exact hres.next.mono hFF
    · simpa [ldStep, Fr1, Fr0] using hJ
    · simp [ldStep]
  case bnd =>
    rnodeW rBnd rBnd_ok bBnd (hW RN.bnd)
    dsimp only [rvN, rvX] at hJ ⊢
    obtain ⟨rfl, hJ, h11⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := rBnd_walk (_root_.Executable.labels exe).label _ hJ h11 hn
    exact .inl ⟨RN.j, by rw [h1, ← ofNat4_add]; rfl, by rw [h2]; rfl, rfl, h3⟩
  case j =>
    rnodeW rJ rJ_ok bJ (hW RN.j)
    dsimp only [rvN, rvX] at hJ ⊢
    rw [rJ_run]
    exact .inl ⟨RN.ok, rfl, rfl, hJ⟩
  case ok =>
    rnodeW rRet rRet_ok bOk (hW RN.ok)
    dsimp only [rvN, rvX] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := rRet_walk (_root_.Executable.labels exe).label _ hJ
    exact .inr ⟨(), h1.symm, by rw [h2]; rfl, rfl, h3⟩

end SegProof

end Spike.Lib.A64.Rt.Reserve

/-- info: 'Spike.Lib.A64.Rt.Reserve.reserve_segWA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Rt.Reserve.reserve_segWA
