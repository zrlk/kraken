/-
**`SFactsS` at a real pair at depth** (x86-64, H7a calls, the call bracket
and its callee): `SFactsS.ofSFactsAt` (`Spike/Lib/X64SFactsS1.lean`) for
owned words that depend on the frames (the own map at depth, holding the
depth word at the frames' count), the owned words' fields at the frames its
runs reach as premises.

- `SFactsS.ofSFactsAtO`: at a `Good1` pair `(c, fs)` of an `Accepted1`
  program, from `SFacts` at `c` at the owned words of the frames `fs`, the
  suspended frames placed (`FramesPlaced`, e.g. `FramesPlacedInI`'s) and
  their environments small (e.g. `framesSmall_callTo`), and the owned
  words' fields (`ownRun`, `ownInstr`, `ownSys`) at the frames reached; the
  source fields from `Spike/Lib/DepthFactsS.lean`.
- `SFactsS.ofSFactsAtI`: the same with the frames placed in slots or
  immediates (`FramesPlacedInI`).
-/
import Spike.Lib.X64SFactsS1
import Spike.Lib.X64FramesPlacedI

namespace Spike.Lib.X64ConsumerS

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer

variable {Λ : Scc.Sem.Layout} {μ : Marks} {p : Prog} {rS : Range} {Tk : State → Prop} {lbl : Lbl}
  {cells ctr : Nat} {s : State} {c : Ctl} {Dt : State → Prop}

/-- **`SFactsS` at the frames `fs` from `SFacts`** at the owned words of
`fs`, at a `Good1` pair of an `Accepted1` program: the current control's
facts, the suspended frames placed (`hfp`) and their environments small
(`hes`), given the owned words' fields at the frames its runs reach. -/
theorem SFactsS.ofSFactsAtO {own : OwnS} {fs : List TermRun.Frame} (h : SFacts Λ μ (fun s => own s fs) rS Tk lbl s c Dt)
    (hp : Scc.Lower.Accepted1 p = true) (hg : Good1 p (c, fs)) (hfp : FramesPlaced Λ lbl s fs)
    (hes : ∀ f ∈ fs, EnvSmall f.env)
    (hownRun : ∀ c₁ fs₁ c₂ fs₂, FrameRun p (c₁, fs₁) (c₂, fs₂) → ((c₁ = c ∧ fs₁ = fs) ∨ (c₂ = c ∧ fs₂ = fs)) →
      own s fs₂ = own s fs₁)
    (hownInstr : ∀ c' fs', FrameRun p (c, fs) (c', fs') → abi.atSys s = false → ∀ tree,
      isa.exec s = some tree → OwnTree (own · fs') (own s fs') tree)
    (hownSys : ∀ c' fs', FrameRun p (c, fs) (c', fs') → abi.atSys s = true → ∀ call,
      Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call → ∀ s' ∈ Kernel.certSuccs abi s call,
        own s' fs' = own s fs') :
    SFactsS Λ μ p own rS Tk lbl cells ctr s c fs Dt where
  noRet := fun _ => h.noRet
  cell := cell_of_good1 hp hg
  noSite := h.noSite
  mapped := h.mapped
  place := PlacedS.ofFrames h.place hfp
  svc := h.svc
  noAlloc := noAlloc_of_good1 hp hg
  ownRun := hownRun
  ownInstr := hownInstr
  ownSys := hownSys
  ownTake := h.ownTake
  site := h.site
  tkTake := h.tkTake
  tkInstr := h.tkInstr
  tkSys := h.tkSys
  owned := h.owned
  abortOk := fun k a ha hpc => by
    obtain ⟨hk, ho, he, hx⟩ := h.abortOk k a ha hpc
    exact ⟨.inl ⟨hk, ho, he, hes⟩, hx⟩
  wrTail := h.wrTail

/-- **`SFactsS` at the frames `fs` from `SFacts`**, the suspended frames
placed in the slots of `A` or at immediates (`FramesPlacedInI`). -/
theorem SFactsS.ofSFactsAtI {own : OwnS} {fs : List TermRun.Frame} {A : Nat → Prop}
    (h : SFacts Λ μ (fun s => own s fs) rS Tk lbl s c Dt)
    (hp : Scc.Lower.Accepted1 p = true) (hg : Good1 p (c, fs)) (hfp : FramesPlacedInI Λ lbl s fs A)
    (hes : ∀ f ∈ fs, EnvSmall f.env)
    (hownRun : ∀ c₁ fs₁ c₂ fs₂, FrameRun p (c₁, fs₁) (c₂, fs₂) → ((c₁ = c ∧ fs₁ = fs) ∨ (c₂ = c ∧ fs₂ = fs)) →
      own s fs₂ = own s fs₁)
    (hownInstr : ∀ c' fs', FrameRun p (c, fs) (c', fs') → abi.atSys s = false → ∀ tree,
      isa.exec s = some tree → OwnTree (own · fs') (own s fs') tree)
    (hownSys : ∀ c' fs', FrameRun p (c, fs) (c', fs') → abi.atSys s = true → ∀ call,
      Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call → ∀ s' ∈ Kernel.certSuccs abi s call,
        own s' fs' = own s fs') :
    SFactsS Λ μ p own rS Tk lbl cells ctr s c fs Dt :=
  SFactsS.ofSFactsAtO h hp hg hfp.toFramesPlaced hes hownRun hownInstr hownSys

end Spike.Lib.X64ConsumerS
