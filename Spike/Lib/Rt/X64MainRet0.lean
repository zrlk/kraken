/-
**Oracle of `mainU_segW` on `ret0`** (`Spike/Lib/Rt/X64Main.lean`): the
hand `scc_rt_main` of `ret0` passes the generic code check, the hand
`wc_main` segment is the generic user-function interface, and the hand
`main_segW`'s premises give the generic theorem's, so that the hand theorem
is re-derived from the generic one (`main_segW_ofU`). The x86-64 twin of
`Spike/Lib/Rt/A64MainRet0.lean`.

- `ret0MC`: frame 32, exit value spilled at `-16`, the user function
  `wc_main`, `scc_rt_main`'s labels and the cells' sizes; `ret0_mainUIn` is
  the code check.
- `ret0_userCallW`: `wc_main`'s obligations (`WcW`) in the callee's region
  give `UserCallW` at `Post c v := c = c0 ∧ v = 42#64`, `ZU = 16`, `D = 24`.
- `mainUW_ofW`: `scc_rt_main`'s own obligations (`MainW`) give `MainUW`;
  the return node differs from the hand one only in the order of its
  conjuncts (`mainURR_ret0`).
-/
import Spike.Lib.Rt.X64Main

namespace Spike.Lib.X64.Rt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Ret0 (MainG MainW mainN0 mainNX mainNRR WcG WcW wc_segW LimOk limA CallerCells)
open Scc.Cert.Rt.X64 (Lays endOf)

/-- **`ret0`'s `scc_rt_main`**: frame 32, the exit value at `-16`,
`wc_main`. -/
def ret0MC : MainCode :=
  ⟨32, -16, "wc_main", ".Lscc_rt_main.chk", ".Lscc_rt_main.stk", ".Lscc_rt_main.entry", ".Lscc_rt_main.x2",
    5, 9, 3, 2, 4, [(.rdi, -8, 4)], 4, 4, 5⟩

/-- `ret0`'s `scc_rt_main` passes the code check. -/
theorem ret0_mainUIn : mainUIn SccCode.ret0Cells ret0MC = true := by
  have hin := Ret0.ret0_mainIn
  simp only [Ret0.mainIn, Bool.and_eq_true] at hin
  simp only [mainUIn, Bool.and_eq_true]
  exact ⟨⟨⟨ret0_mainPro, hin.1⟩, hin.2⟩, ret0_mainExit⟩

/-- `ret0`'s user post: the source control unmoved, `%rax = 42`. -/
def ret0Post (c0 : Ctl) (c : Ctl) (v : BitVec 64) : Prop := c = c0 ∧ v = 42#64

/-- The generic return node on `ret0` is the hand one (its conjuncts
reordered). -/
theorem mainURR_ret0 (lab : Label → Int64) (g : MainG) :
    mainURR lab ret0MC (ret0Post g.c0) = mainNRR lab g := by
  simp only [mainURR, mainNRR, mainUR, Ret0.mainNR, ret0Post, ret0MC]
  congr 1
  funext σ c
  rw [show -8 - (-8 - (32 : Int64).toInt) = -8 - -40 from rfl]
  exact propext ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h3, h2⟩, fun ⟨h1, h3, h2⟩ => ⟨⟨h1, h2⟩, h3⟩⟩

section Oracle

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wc_main` is `ret0`'s user function**: its obligations in the
callee's region of depth 24 below the return address, under `scc_rt_main`'s
frame of 32, give the interface at `ret0Post`, `ZU = 16`. -/
theorem ret0_userCallW {W : Frag isa} {K : State → State → Prop} (hp : Lays exe SccCode.ret0Cells)
    (hend : endPc = endOf exe SccCode.ret0Cells) {ra : BitVec 64} {c0 : Ctl} {tp : UInt64}
    (hwc : ∀ g' : WcG, g'.ra = ra → g'.c0 = c0 → g'.tp = tp →
      WcW W K exe endPc (R.callee (-48 - 0) (-24) 8) (fun m => F m ∧ CallerCells R (-48 - 0) (-24) 8 m) ms g') :
    UserCallW W K p lbl ms exe endPc R F "wc_main" 32 24 16 (ret0Post c0) ra c0 tp := by
  intro F' hR' hF' hFF g hra hc htp
  exact (wc_segW hp hend hF' hR' (Int.le_refl _) (Int.le_refl _) (fun m h => (hFF m h).1) g
    ((hwc g hra hc htp).mono hFF)).mono_post fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hc', h42, hb, hs⟩ =>
      ⟨he, hn, hdc, hpc, σ, hA, hD, ⟨hc'.trans hc, h42⟩, hb, hs⟩

omit [Kraken.Executable.ValidLayout exe] in
/-- **`scc_rt_main`'s own obligations on `ret0`** are the generic ones. -/
theorem mainUW_ofW {W : Frag isa} {K : State → State → Prop} {g : MainG}
    (hW : MainW W K exe endPc R F ms g) : MainUW W K exe endPc R F ms ret0MC (ret0Post g.c0) g :=
  ⟨hW.pro, hW.call, by rw [mainURR_ret0]; exact hW.exit⟩

/-- **The hand `main_segW` from the generic `mainU_segW`**: the same
statement, its premises giving the generic theorem's. -/
theorem main_segW_ofU {W : Frag isa} {K : State → State → Prop} (hp : Lays exe SccCode.ret0Cells)
    (hend : endPc = endOf exe SccCode.ret0Cells)
    (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -72) (hhi : 0 ≤ R.hi) (g : MainG)
    (hlimM : LimOk ms F (limA g.tp) (g.sp0 - 8#64 - (32 : Int64).toBitVec))
    (hlimW : LimOk ms F (limA g.tp) (g.sp0 - 8#64 - (32 : Int64).toBitVec - 8#64 - 8#64 - (16 : Int64).toBitVec))
    (hexit : ∀ s, At exe endPc R F (mainNX (_root_.Executable.labels exe).label) s g.c0 → ¬ ms.abortAt s →
      MainExit p ms s g.c0 42)
    (hW : MainW W K exe endPc R F ms g)
    {Q : Frag isa} :
    SegW W K p lbl ms (At exe endPc R F (mainN0 (_root_.Executable.labels exe).label g)) Q :=
  mainU_segW (mc := ret0MC) (D := 24) (ZU := 16) (Post := ret0Post g.c0) hp hend ret0_mainUIn (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hK hF hR (by show R.lo ≤ -72; exact hlo) hhi g
    hlimM hlimW (ret0_userCallW hp hend hW.wc)
    (fun s c v ⟨hc, hv⟩ hAt hab => by subst hc hv; exact hexit s hAt hab)
    (mainUW_ofW hW)

end Oracle

end Spike.Lib.X64.Rt
