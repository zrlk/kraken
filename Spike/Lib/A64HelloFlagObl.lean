/-
**The flag at every node of the spawned child's run** (AArch64):
`SegRP.ZObl (FlagZ.FlagF cS)`, the `hf` input of `FlagZ.ZObl.flag` / `XH.zObl_XHF`, given the packet's flag
word is `cS`'s locative (`hcS`); every `PrW` control is at a term of `print`'s or `printL`'s body
(`FlagR.prW_pTerm`, `PrW`'s term conjunct).

`FlagF` reads only the control and the frames, so each node obligation is the flag at the node's pinned
control (`blk_ofCtl`, `nodeW_ofCtl`, `proW_ofCtl`, `abortObl_ofCtl`): the child's stub, the thread worker's
prologue and head at `kidH` (`flagF_kidH`, through the prelude's local run to `wcP`); `wc_worker`'s prologue,
head and call at `wcP` (`FlagSrc.flagF_wcP`); `print`'s nodes and its abort path on `uFrame` at `PrW`
controls (`FlagSrc.flagF_pTerm`); the tail and `scc_rt_unpark` at `wcR`, `cS1`, `cS2` (`FlagSrc.flagF_wcRE`,
`flagF_cS1`, `FlagSrc.flagF_cS2`); the thread worker's tail at `cS2`.

- `blk_ofCtl`, `nodeW_ofCtl`, `proW_ofCtl`, `abortObl_ofCtl`: node obligations of a fragment that holds at the
  node's controls.
- `flagF_back`, `flagF_backRun`, `flagF_kidH`: the flag back along the prelude (no access on its terms).
- `flagF_cS1`: the flag at the `unpark` (no step on no frame).
- `cN_prW`: `print`'s nodes at `PrW` are at `PrW` controls.
- `zObl_flag`: `ZObl (FlagF cS)`.
-/
import Spike.Lib.A64HelloFlagR

namespace Spike.Lib.A64.Flow.Worker.Hello.FlagObl

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Worker
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloSplit (wcP wcR kid_splitH worker_find)
open Spike.Lib.HelloWorkerCallSrc (PrW KcW callI_inv)
open Spike.Lib.HelloW1 (uFrame)
open Spike.Lib.WakeMappedRow (LabPtr)
open Spike.Lib.A64.Flow.Worker.Hello.Child (Words)
open Spike.Lib.A64.Flow.Worker.Hello.SegR (kidH cS1 cS2)
open Spike.Lib.A64.Flow.Worker.Hello.SegRP (WcObl ZObl)
open Spike.Lib.A64.Flow.Worker.Hello.FlagZ (FlagF)
open Spike.Lib.A64.Flow.Worker.Hello.FlagSrc (PTermP noLabB noPtr_noLab flagF_wcP flagF_pTerm flagF_wcRE
  flagF_cS2)

/-! ## Node obligations of a fragment of the control -/

section Gen

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {X : Frag isaLSE2}

/-- A fragment at `c0` is one at every control equal to it. -/
theorem of_eq {c c0 : Ctl} (h : ∀ s, X s c0) (e : c = c0) : ∀ s, X s c := e ▸ h

/-- **A block node inside a fragment holding at its controls.** -/
theorem blk_ofCtl {n : ND} {blk : List Directive} (h : ∀ σ c, n.J σ c → ∀ s, X s c) :
    NodeZA X exe endPc R F n blk :=
  fun _ σ c _ _ _ _ _ _ hJ _ _ _ _ _ => ⟨h σ c hJ _, fun _ h => h⟩

/-- **A node inside a fragment holding at its controls.** -/
theorem nodeW_ofCtl {n : ND} (h : ∀ σ c, n.J σ c → ∀ s, X s c) : NodeW X (fun _ _ => False) exe endPc R F n :=
  fun s c hA => ⟨by obtain ⟨-, -, -, -, σ, -, -, hJ⟩ := hA; exact h σ c hJ s, fun _ h => h⟩

/-- **A prologue inside a fragment holding at its entry's controls.** -/
theorem proW_ofCtl {ms : MemSide isaLSE2} {pc0 Z lim : Int64} {L : Label} {ps : List (XReg × Int64)}
    {J : AS → Ctl → Prop} (h : ∀ σ c, J σ c → ∀ s, X s c) :
    ProW X (fun _ _ => False) exe endPc R F ms pc0 Z lim L ps J :=
  ⟨blk_ofCtl h, nodeW_ofCtl fun _ c ⟨σ0, hJ, _⟩ => h σ0 c hJ, blk_ofCtl fun _ c ⟨σ0, _, hJ, _⟩ => h σ0 c hJ,
    blk_ofCtl fun _ c ⟨σ0, _, hJ, _⟩ => h σ0 c hJ⟩

/-- **The write abort path inside a fragment holding at its source control.** -/
theorem abortObl_ofCtl {c0 : Ctl} (h : ∀ s, X s c0) : AbortObl X exe endPc R F c0 where
  de := blk_ofCtl fun _ _ hJ => of_eq h hJ.1
  dt1 := blk_ofCtl fun _ _ hJ => of_eq h hJ.1
  dj1 := blk_ofCtl fun _ _ hJ => of_eq h hJ.1
  dt2 := blk_ofCtl fun _ _ hJ => of_eq h hJ.1
  dj2 := blk_ofCtl fun _ _ hJ => of_eq h hJ.1
  dt3 := blk_ofCtl fun _ _ hJ => of_eq h hJ.1
  dj3 := blk_ofCtl fun _ _ hJ => of_eq h hJ.1
  dt4 := blk_ofCtl fun _ _ hJ => of_eq h hJ.1
  dg4 := blk_ofCtl fun _ _ hJ => of_eq h hJ
  se := blk_ofCtl fun _ _ hJ => of_eq h hJ
  sn1 := nodeW_ofCtl fun _ _ hJ => of_eq h hJ
  sn1b := nodeW_ofCtl fun _ _ hJ => of_eq h hJ
  sn2 := blk_ofCtl fun _ _ hJ => of_eq h hJ
  svc := nodeW_ofCtl fun _ _ hJ => of_eq h hJ.1
  sn5 := blk_ofCtl fun _ _ hJ => of_eq h hJ
  sex := nodeW_ofCtl fun _ _ hJ => of_eq h hJ.1

end Gen

/-! ## The flag along the prelude and at the `unpark` -/

variable {cS : WeakMem.Address} {w0 w1 w2 w3 w4 : TermRun.Word}

/-- The flag at `c0` is the flag at every control equal to it. -/
theorem ofEqF {c c0 : Ctl} {fs : List TermRun.Frame} (h : ∀ s, FlagF cS s c0 fs) (e : c = c0) :
    ∀ s, FlagF cS s c fs := e ▸ h

/-- **The flag back over a local step** from a control accessing nothing. -/
theorem flagF_back {c c₁ : Ctl} {fs : List TermRun.Frame} {s : State} (h : LocalStepS helloSrc c c₁)
    (hn : noLabB c.term = true) (hf : FlagF cS s c₁ fs) : FlagF cS s c fs := by
  intro c₂ fs₂ hr sa hp
  cases hr with
  | refl => exact (noPtr_noLab hn sa hp).elim
  | step hs hr' =>
    obtain rfl := PrintSvc.FrameStep.of_local h hs
    exact hf c₂ fs₂ hr' sa hp

/-- The prelude's and `print`'s terms access nothing. -/
theorem pTermT_noLab {e : Expr} (h : HelloW1.PTermT e) : noLabB e = true := by
  rcases h with h | h
  · have h1 : HelloW1.preTermsH.all noLabB = true := by decide
    exact List.all_eq_true.1 h1 e h
  · exact FlagSrc.pTermP_noLab h

/-- **The flag back over a local run through the prelude's and `print`'s terms.** -/
theorem flagF_backRun {c c₁ : Ctl} {fs : List TermRun.Frame} {s : State} (h : LocalRunS helloSrc c c₁)
    (ht : HelloW1.PTermT c.term) (hf : FlagF cS s c₁ fs) : FlagF cS s c fs := by
  induction h with
  | refl => exact hf
  | step hs _ ih => exact flagF_back hs (pTermT_noLab ht) (ih (HelloW1.pTermT_step hs ht) hf)

/-- **The flag at the spawned child's control** (its tail call into `worker`). -/
theorem flagF_kidH (hcS : w3.val = .loc cS 0) (T : Ty) (s : State) : FlagF cS s (kidH T w0 w1 w2 w3 w4) [] :=
  flagF_backRun (kid_splitH worker_find w0 w1 w2 w3 w4) (.inl (by simp [HelloW1.preTermsH, kidH]))
    (flagF_wcP hcS s)

/-- **The flag at the `unpark`, on no frame**: the extern takes no local step, calls nothing, and there is
no frame to return into; the `unpark` accesses nothing. Any `cS`. -/
theorem flagF_cS1 (cS : WeakMem.Address) (w0 w1 w2 w3 w4 : TermRun.Word) (s : State) :
    FlagF cS s (cS1 w0 w1 w2 w3 w4) [] := by
  intro c₁ fs₁ hr sa h
  cases hr with
  | refl => exact (noPtr_noLab (c := cS1 w0 w1 w2 w3 w4) rfl sa h).elim
  | step hs _ =>
    cases hs with
    | loc hl => exact (PrintSvc.LocalStepS.not_ext hl rfl).elim
    | call hc => simp [cS1] at hc

/-! ## `print`'s nodes -/

/-- A system call's result keeps the source at `P`. -/
theorem rc0_P {len0 k : Nat} {P : Nat → Ctl → Prop} {r : BitVec 64} {c : Ctl} (h : PrintA.RC0 len0 P P k r c) :
    ∃ j, P j c := by
  rcases h with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, h⟩ <;> exact ⟨_, h⟩

theorem rc1_P {len0 k : Nat} {P : Nat → Ctl → Prop} {r : BitVec 64} {c : Ctl} (h : PrintA.RC1 len0 P P k r c) :
    ∃ j, P j c := by
  rcases h with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, h⟩ <;> exact ⟨_, h⟩

theorem rc2_P {len0 k : Nat} {P : Nat → Ctl → Prop} {r : BitVec 64} {c : Ctl} (h : PrintA.RC2 len0 P P k r c) :
    ∃ j, P j c := by
  rcases h with ⟨-, -, h⟩ | ⟨-, h⟩ <;> exact ⟨_, h⟩

/-- **`print`'s nodes at `P` are at `P` controls.** -/
theorem cN_P {lab : Label → Int64} {P : Nat → Ctl → Prop} {σC σ : AS} {c : Ctl} {i : PrintF.PN}
    (h : (PrintF.cN lab (fun _ => P) (fun _ => P) σC i).J σ c) : ∃ j, P j c := by
  obtain ⟨h, -⟩ := h
  cases i
  case e => exact ⟨_, h.1⟩
  case n1 | loop => obtain ⟨_, -, h⟩ := h; exact ⟨_, h⟩
  case n3 | fence | write => obtain ⟨_, -, -, h⟩ := h; exact ⟨_, h⟩
  case svc => obtain ⟨⟨_, -, -, h⟩, -⟩ := h; exact ⟨_, h⟩
  case n5 => obtain ⟨_, -, h⟩ := h; exact rc0_P h
  case n6 => obtain ⟨⟨_, -, h⟩, -⟩ := h; exact rc0_P h
  case n7 | chk2 => obtain ⟨_, -, h⟩ := h; exact rc1_P h
  case n9 => obtain ⟨⟨_, -, h⟩, -⟩ := h; exact rc1_P h
  case n10 | chk3 => obtain ⟨_, -, h⟩ := h; exact rc2_P h
  case n12 | adv => obtain ⟨_, -, -, -, h⟩ := h; exact ⟨_, h⟩
  case fail => obtain ⟨_, h⟩ := h; exact ⟨_, h⟩
  case done => exact ⟨_, h.2.2⟩

/-! ## `ZObl` at the flag -/

variable {exe : _root_.Executable} {endPc : Int64} {ms : List TermRun.Frame → MemSide isaLSE2} {w : Words}
  {tp sp0 : BitVec 64} {n m : Nat}

/-- **`WcObl` at the flag**: every node of `wc_worker` at its pinned control. -/
theorem wcObl_flag (hcS : w3.val = .loc cS 0)
    (R' : Region) (F' : MachineData → Prop) (x29 ra : BitVec 64) :
    WcObl (FlagF cS) exe endPc ms R' F' x29 ra w tp sp0 w0 w1 w2 w3 w4 n m where
  hz := proW_ofCtl fun _ _ hJ => ofEqF (flagF_wcP hcS) hJ.1.1
  hZE := blk_ofCtl fun _ _ hJ => ofEqF (flagF_wcP hcS) hJ.1
  hZC := nodeW_ofCtl fun _ _ hJ => ofEqF (flagF_wcP hcS) hJ.2.1
  hZP := by
    intro fr _ _ _ _ _ _ _ _ _ σC c cE hJ hci i
    obtain rfl := hJ.2.1
    obtain ⟨-, rfl⟩ := callI_inv hci
    exact blk_ofCtl fun _ _ hJ' s => let ⟨_, hP⟩ := cN_P hJ'; flagF_pTerm hcS (FlagR.prW_pTerm hP) s
  hZA := by
    intro fr _ _ _ _ _ _ _ _ _ σC c cE hJ hci k c' hP
    obtain rfl := hJ.2.1
    obtain ⟨-, rfl⟩ := callI_inv hci
    exact abortObl_ofCtl (flagF_pTerm hcS (FlagR.prW_pTerm hP))
  hZW i := blk_ofCtl fun _ _ hJ => by
    cases i
    case sp4 => exact ofEqF (flagF_wcRE hcS []) hJ.1
    case st => exact ofEqF (flagF_wcRE hcS []) hJ.1.1
    case n3 => exact ofEqF (flagF_cS1 cS w0 w1 w2 w3 w4) hJ.1
    case bl | unpk => exact ofEqF (flagF_cS1 cS w0 w1 w2 w3 w4) hJ.1.1
    case sp6 => exact ofEqF (flagF_cS2 cS w0 w1 w2 w3 w4) hJ.1
  hZU _ _ _ _ _ _ _ _ _ _ _ i := blk_ofCtl fun _ _ hJ => by
    cases i
    case e | n1 => exact ofEqF (flagF_cS1 cS w0 w1 w2 w3 w4) hJ.1
    case swp => exact ofEqF (flagF_cS1 cS w0 w1 w2 w3 w4) hJ.1.1
    case svc => exact ofEqF (flagF_cS2 cS w0 w1 w2 w3 w4) hJ.1.1
    all_goals exact ofEqF (flagF_cS2 cS w0 w1 w2 w3 w4) hJ.1

/-- **`ZObl` at the flag** (row B8-hflag-ZObl): the stub and the thread worker's head at `kidH`, its tail
at `cS2`, `wc_worker` by `wcObl_flag`. -/
theorem zObl_flag {R : Region} {F : MachineData → Prop} {T : Ty} (hcS : w3.val = .loc cS 0) :
    ZObl (FlagF cS) exe endPc ms R F w tp sp0 T w0 w1 w2 w3 w4 n m where
  hZc i := blk_ofCtl fun _ _ hJ => by
    cases i
    case cb => exact ofEqF (flagF_kidH hcS T) hJ.1
    case ch => obtain ⟨_, hJ⟩ := hJ; exact ofEqF (flagF_kidH hcS T) hJ.1
  hzT := proW_ofCtl fun _ _ hJ => ofEqF (flagF_kidH hcS T) hJ.1
  hZEt := blk_ofCtl fun _ _ hJ => ofEqF (flagF_kidH hcS T) hJ.1
  hZT i := blk_ofCtl fun _ _ hJ => by
    cases i <;> first
      | exact ofEqF (flagF_cS2 cS w0 w1 w2 w3 w4) hJ
      | exact ofEqF (flagF_cS2 cS w0 w1 w2 w3 w4) hJ.1
  hwc R' F' _ _ _ _ _ _ x29 ra _ := wcObl_flag hcS R' F' x29 ra

/-- `hcS` is met by the flag's own locative word: the flag at the spawned child, non-vacuously. -/
example (cS : WeakMem.Address) (T : Ty) (w0 w1 w2 w4 : TermRun.Word) (s : State) :
    FlagF cS s (kidH T w0 w1 w2 (TermRun.cst (.loc cS 0)) w4) [] :=
  flagF_kidH rfl T s

end Spike.Lib.A64.Flow.Worker.Hello.FlagObl

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.FlagObl.zObl_flag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.FlagObl.zObl_flag
