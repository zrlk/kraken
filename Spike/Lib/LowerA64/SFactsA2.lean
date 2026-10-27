/-
**The per-pair facts of an `Accepted2` program's pairs** (AArch64; the twin
of `Spike/Lib/LowerX64/SFactsA2.lean`): the allocation-capable consumer's
`SFactsA` (`Spike/Lib/A64SegInstA.lean`) gathered as the state's facts
(`SFactsSt`, `AbSt`, `Spike/Lib/A64SFactsA.lean`) and the pair's, at owned
words with no frame dependence, the frame runs' cell and zero obligations
from `RunOk2` (`Spike/Lib/Src/RunOk2.lean`).

- `W2`: the facts at `(s, c, fs)`;
- `sfactsA_of_W2`: `SFactsA` from them (`SFactsA.ofSt`);
- `w2_of`: `W2` from the state's facts, an `Accepted2` program's pair free
  of `ZBad` (`FrOk2`, `runOk2_of`) and the remaining pair facts.
-/
import Spike.Lib.A64SFactsA
import Spike.Lib.PrintSvc
import Spike.Lib.Src.RunOk2

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.LowerNode (RunOk2 FrOk2 ZBad runOk2_of)

/-- **The facts at an `Accepted2` program's pair** `(c, fs)` with the
state `s`, at owned words `own` not depending on the frames:
- `st`, `ab`: the state's (`SFactsSt`, `AbSt`);
- `noRet`: `main`'s `ret` excluded at no frame;
- `run`: the frame runs' cell and zero obligations (`RunOk2`);
- `place`: the frames placed, or the current frame in the output extern's
  model (`PlacedSE`);
- `wr`: at every pair a frame run reaches, off a system call, the arena's
  write obligation (`SFactsA.wr`);
- `abort`: the abort sites (`SFactsA.abortOk`);
- `svc1`: at an output `write(1, …)`, the source at `print`'s loop top
  inside a call (`PrintSvc`). -/
structure W2 (Λ : Scc.Sem.Layout) (μ : Marks) (p : Prog) (rd : TermRun.Word → Prop) (G : Loc → Val → Prop)
    (own : Own) (rS : Range) (Tk : State → Prop) (ar : Arena) (J : InvS) (Dt Ab : State → Prop) (lbl : Lbl)
    (lsize : Lsize) (s : State) (c : Ctl) (fs : List TermRun.Frame) : Prop where
  st : SFactsSt Λ μ own rS Tk s Dt
  ab : AbSt μ Ab s
  noRet : fs = [] → ∀ a, c.term ≠ .ret a
  run : RunOk2 p c fs
  place : PlacedSE Λ lbl s c fs
  wr : ∀ c' fs', FrameRun p (c, fs) (c', fs') → abi.atSys s = false →
    WrOkA ar lbl lsize (msOfA Λ μ rd G (fun s _ => own s) ar J lbl lsize fs')
      (fun s' c'' => PendA p J lbl lsize s' c'' fs') s c'
  abort : ∀ k a, μ.abortAt k = some a → pcOf s = a →
    ((k = .writeErr ∧ Ab s) ∨ (k = .overflow ∧ OvfReady c ∧ EnvSmallS c.env fs) ∨
      (k = .heap ∧ HeapAbortObl ar.cells ar.ctr c)) ∧
      ∀ v, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.exitGroup v) → v % 256 = Kernel.abortStatus
  svc1 : abi.atSys s = true → ∀ b n, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.write 1 b n) →
    Spike.Lib.PrintSvc.PrintSvc c fs

variable {Λ : Scc.Sem.Layout} {μ : Marks} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own : Own} {rS : Range} {Tk : State → Prop} {ar : Arena} {J : InvS} {Dt Ab : State → Prop} {lbl : Lbl}
  {lsize : Lsize} {s : State} {c : Ctl} {fs : List TermRun.Frame}

/-- **`SFactsA` from `W2`**, at the owned words `fun s _ => own s`. -/
theorem sfactsA_of_W2 (h : W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs) :
    SFactsA Λ μ p rd G (fun s _ => own s) rS Tk ar J lbl lsize s c fs Dt Ab :=
  SFactsA.ofSt h.st h.ab h.noRet h.run.cell h.place h.wr h.run.zero h.abort

/-- **`W2` at a pair free of `ZBad`** of a program whose blocks are
(`ProgNoS ZBad p`, from `progNoS_zbad_of_accepted2`). -/
theorem w2_of (hp : ProgNoS ZBad p) (hf : FrOk2 c fs) (hst : SFactsSt Λ μ own rS Tk s Dt) (hab : AbSt μ Ab s)
    (hnr : fs = [] → ∀ a, c.term ≠ .ret a) (hpl : PlacedSE Λ lbl s c fs)
    (hwr : ∀ c' fs', FrameRun p (c, fs) (c', fs') → abi.atSys s = false →
      WrOkA ar lbl lsize (msOfA Λ μ rd G (fun s _ => own s) ar J lbl lsize fs')
        (fun s' c'' => PendA p J lbl lsize s' c'' fs') s c')
    (habort : ∀ k a, μ.abortAt k = some a → pcOf s = a →
      ((k = .writeErr ∧ Ab s) ∨ (k = .overflow ∧ OvfReady c ∧ EnvSmallS c.env fs) ∨
        (k = .heap ∧ HeapAbortObl ar.cells ar.ctr c)) ∧
        ∀ v, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.exitGroup v) → v % 256 = Kernel.abortStatus)
    (hsvc : abi.atSys s = true → ∀ b n, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.write 1 b n) →
      Spike.Lib.PrintSvc.PrintSvc c fs) :
    W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs :=
  ⟨hst, hab, hnr, runOk2_of hp hf, hpl, hwr, habort, hsvc⟩

/--
info: 'Spike.Lib.LowerA64.sfactsA_of_W2' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sfactsA_of_W2

end Spike.Lib.LowerA64
