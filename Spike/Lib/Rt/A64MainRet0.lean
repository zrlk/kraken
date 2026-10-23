/-
**Oracle of `mainU_segW` on `ret0`** (`Spike/Lib/Rt/A64Main.lean`): the
hand `scc_rt_main` of `ret0` passes the generic code check, the hand
`wc_main` segment is the generic user-function interface, and the hand
`main_segW`'s premises give the generic theorem's, so that the hand theorem
is re-derived from the generic one (`main_segW_ofU`).

- `ret0MC`: frame 48, exit value spilled at 8, the user function `wc_main`,
  and `scc_rt_main`'s labels; `ret0_mainUIn` is the code check.
- `ret0_userCallW`: `wc_main`'s obligations (`WcW`) in the callee's region
  give `UserCallW` at `Post c v := c = c0 ∧ v = 42#64`, `ZU = D = 32`.
- `mainUW_ofW`: `scc_rt_main`'s own obligations (`MainW`) give `MainUW`.
-/
import Spike.Lib.Rt.A64Main

namespace Spike.Lib.A64.Rt

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (MainG MainW mainN0 mainNX WcG WcW wc_segW LimOk limA CallerCells)
open Scc.Cert.Rt.A64 (Lays endOf)

/-- **`ret0`'s `scc_rt_main`**: frame 48, the exit value at 8, `wc_main`. -/
def ret0MC : MainCode :=
  ⟨48, 8, "wc_main", ".L1_scc_rt_main.stack_check", ".L1_scc_rt_main.stack_grow", ".L1_scc_rt_main.0_entry",
    ".L1_scc_rt_main.sp0"⟩

/-- `ret0`'s `scc_rt_main` passes the code check. -/
theorem ret0_mainUIn : mainUIn SccCode.ret0Prog ret0MC = true := by
  have hin := Ret0.ret0_mainIn
  simp only [Ret0.mainIn, Bool.and_eq_true] at hin
  simp only [mainUIn, Bool.and_eq_true]
  exact ⟨⟨⟨ret0_mainPro, hin.1⟩, hin.2⟩, ret0_exitIn⟩

/-- `ret0`'s user post: the source control unmoved, `x0 = 42`. -/
def ret0Post (c0 : Ctl) (c : Ctl) (v : BitVec 64) : Prop := c = c0 ∧ v = 42#64

section Oracle

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **`wc_main` is `ret0`'s user function**: its obligations in the
callee's region of depth 32 below `scc_rt_main`'s frame of 48 give the
interface at `ret0Post`, `ZU = D = 32`. -/
theorem ret0_userCallW {W : Frag isaLSE2} {K : State → State → Prop} (hp : Lays exe SccCode.ret0Prog)
    (hend : endPc = endOf exe SccCode.ret0Prog) {ra : BitVec 64} {c0 : Ctl} {tp : UInt64}
    (hwc : ∀ g' : WcG, g'.ra = ra → g'.c0 = c0 → g'.tp = tp →
      WcW W K exe endPc (R.callee (-48) (-32) 0) (fun m => F m ∧ CallerCells R (-48) (-32) 0 m) ms g') :
    UserCallW W K p lbl ms exe endPc R F "wc_main" 48 32 32 (ret0Post c0) ra c0 tp := by
  intro F' hR' hal' hF' hFF g hra hc htp
  exact (wc_segW hp hend hF' hR' hal' (Int.le_refl _) (Int.le_refl _) (fun m h => (hFF m h).1) g
    ((hwc g hra hc htp).mono hFF)).mono_post fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hc', h42, h29, h30⟩ =>
      ⟨he, hn, hdc, hpc, σ, hA, hD, ⟨hc'.trans hc, h42⟩, h29, h30⟩

omit [Kraken.Executable.ValidLayout exe] in
/-- **`scc_rt_main`'s own obligations on `ret0`** are the generic ones. -/
theorem mainUW_ofW {W : Frag isaLSE2} {K : State → State → Prop} {g : MainG}
    (hW : MainW W K exe endPc R F ms g) : MainUW W K exe endPc R F ms ret0MC (ret0Post g.c0) g :=
  ⟨hW.pro, hW.call, hW.exit⟩

/-- **The hand `main_segW` from the generic `mainU_segW`**: the same
statement, its premises giving the generic theorem's. -/
theorem main_segW_ofU {W : Frag isaLSE2} {K : State → State → Prop} (hp : Lays exe SccCode.ret0Prog)
    (hend : endPc = endOf exe SccCode.ret0Prog)
    (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi) (g : MainG)
    (hlimM : LimOk ms F exe endPc (limA g.tp) (g.sp0 - (48 : Int64).toBitVec))
    (hlimW : LimOk ms F exe endPc (limA g.tp) (g.sp0 - (48 : Int64).toBitVec - (32 : Int64).toBitVec))
    (hexit : ∀ s, At exe endPc R F (mainNX (_root_.Executable.labels exe).label) s g.c0 → ¬ ms.abortAt s →
      MainExit p ms s g.c0 42)
    (hW : MainW W K exe endPc R F ms g)
    {Q : Frag isaLSE2} :
    SegW W K p lbl ms (At exe endPc R F (mainN0 (_root_.Executable.labels exe).label g)) Q :=
  mainU_segW (mc := ret0MC) (D := 32) (ZU := 32) (Post := ret0Post g.c0) hp hend ret0_mainUIn (by decide)
    (by decide) (by decide) (by decide) (by decide) hK hF hR hal (by show R.lo ≤ -80; exact hlo) hhi g hlimM hlimW
    (ret0_userCallW hp hend hW.wc)
    (fun s c v ⟨hc, hv⟩ hAt hab => by subst hc hv; exact hexit s hAt hab)
    (mainUW_ofW hW)

end Oracle

end Spike.Lib.A64.Rt
